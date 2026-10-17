import PfaffianDescent.CorayGlobalNormalizationSupportClosed
import PfaffianDescent.CorayPerfectFiniteTypeNormalization

/-! SOURCE ONLY / UNVERIFIED. ACTUAL normalization quotient closed support
for ORIGINAL perfect K, from actual finite normalization094 and native
coherent-module support. Same normalization, quotient and pi-induced maps.
No curve-dimension, finite-support, H1 or genus conclusion is a premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

theorem perfectField_genericNormalizationQuotientSheaf_affineStalkSupport_isClosed
    {K : Type u} [Field K] [PerfectField K]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsClosed (schemeModuleStalkSupport
      ((Scheme.Modules.restrictFunctor U.ι).obj (genericNormalizationQuotientSheaf X))) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : Algebra Γ(X, U) Γ((X.fromSpecStalk (genericPoint X)).normalization, ν ⁻¹ᵁ U) :=
    (ν.app U).hom.toAlgebra
  let A := Γ(X, U)
  let beta : K →+* A :=
    (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  letI : Algebra K A := beta.toAlgebra
  have hbeta : beta.FiniteType := RingHom.FiniteType.comp
    (pi.finiteType_appLE (isAffineOpen_top _) hU (by simp))
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  letI : Algebra.FiniteType K A := hbeta
  letI : IsFractionRing A X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  letI : Module.Finite A (integralClosure A (FractionRing A)) :=
    finiteNormalization_of_finiteType_perfectField K A
  letI : Module.Finite A (integralClosure A X.functionField) :=
    Module.Finite.equiv (FractionRing.algEquiv (A := A) X.functionField).mapIntegralClosure.toLinearEquiv
  letI : Module.Finite A (localNormalizationDefect A X.functionField) := inferInstance
  letI : IsAffine (ν ⁻¹ᵁ U).toScheme := genericNormalization_affinePreimage_isAffine X U hU
  let Q := genericNormalizationQuotientSheaf X
  let MU := (Scheme.Modules.restrictFunctor U.ι).obj Q
  let e := hU.isoSpec
  let F := Scheme.Modules.pushforward e.hom
  let G := moduleSpecΓFunctor (R := A)
  let P := F.obj MU
  let qU := SheafOfModules.unitToPushforwardObjUnit (ν ∣_ U).toRingCatSheafHom
  let N := F.obj (cokernel qU)
  let C : P ≅ N := F.mapIso (genericNormalizationQuotientSheaf_restrictIso X U)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := A) N) :=
    affineIsoTargetQuotientSheaf_fromTildeGamma_isIso (ν ∣_ U) e
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := A) P) :=
    isIso_fromTildeΓ_iff.mpr
      ⟨G.obj N, ⟨asIso (Scheme.Modules.fromTildeΓ (R := A) N) ≪≫ C.symm⟩⟩
  let eSections : G.obj P ≅ ModuleCat.of A (localNormalizationDefect A X.functionField) :=
    affineOpenSpecPushforward_sectionsIso X U hU Q ≪≫
      genericNormalizationQuotientSheaf_affineSectionsIso X U hU
  have hP : IsClosed (schemeModuleStalkSupport P) := by
    rw [schemeModuleStalkSupport_eq_of_iso
      (asIso (Scheme.Modules.fromTildeΓ (R := A) P)).symm,
      tilde_actualStalkSupport_eq]
    change IsClosed (Module.support A (G.obj P))
    rw [moduleSupport_eq_of_linearEquiv eSections.toLinearEquiv]
    exact Module.isClosed_support
  have hMU : schemeModuleStalkSupport
      ((Scheme.Modules.restrictFunctor e.hom).obj P) = schemeModuleStalkSupport MU :=
    schemeModuleStalkSupport_eq_of_iso
      ((Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app MU)
  change IsClosed (schemeModuleStalkSupport MU)
  rw [← hMU, schemeModuleStalkSupport_restrict]
  exact hP.preimage e.hom.continuous

/-- ACTUAL canonical GLOBAL normalization quotient of an integral scheme
locally of finite type over a perfect field has CLOSED ACTUAL
nonzero-stalk support. Every affine support and comparison is derived. -/
theorem perfectField_integralScheme_genericNormalizationQuotient_stalkSupport_isClosed
    {K : Type u} [Field K] [PerfectField K]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    IsClosed (schemeModuleStalkSupport (genericNormalizationQuotientSheaf X)) := by
  let Y : X.affineOpens → Scheme.{u} := fun U => U.1.toScheme
  let f : ∀ U : X.affineOpens, Y U ⟶ X := fun U => U.1.ι
  have hcover : ∀ x : X, ∃ U, ∃ y : Y U, f U y = x := by
    intro x
    have hx : x ∈ ⨆ U : X.affineOpens, (U : X.Opens) := by
      rw [iSup_affineOpens_eq_top]
      trivial
    obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp hx
    exact ⟨U, ⟨x, hxU⟩, rfl⟩
  apply schemeModuleStalkSupport_isClosed_of_open_cover
    (genericNormalizationQuotientSheaf X) Y f hcover
  intro U
  by_cases hnonempty : Nonempty U.1
  · letI : Nonempty U.1 := hnonempty
    exact perfectField_genericNormalizationQuotientSheaf_affineStalkSupport_isClosed X pi U.1 U.2
  · have hempty : schemeModuleStalkSupport
        ((Scheme.Modules.restrictFunctor (f U)).obj (genericNormalizationQuotientSheaf X)) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hnonempty ⟨y⟩
    rw [hempty]
    exact isClosed_empty

end PfaffianDescent.Coray
