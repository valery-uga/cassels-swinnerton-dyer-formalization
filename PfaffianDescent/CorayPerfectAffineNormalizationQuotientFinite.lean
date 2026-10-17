import PfaffianDescent.CorayGlobalOriginalSectionsFinite
import PfaffianDescent.CorayProjectiveGlobalNormalizationSupport
import PfaffianDescent.CorayPerfectFiniteTypeNormalization

/-! Actual affine normalization quotient over ORIGINAL perfect K. Finite
normalization is constructed by the inseparable-safe finite-type producer;
the genuine denominator torsion then gives finite original-K sections and
finite native nonzero-stalk support. The literal normalization, quotient and
pi-induced scalar actions remain unchanged. No H1 finiteness, genus, Serre
vanishing, or supplied finite-normalization conclusion is an input.
SOURCE ONLY / UNVERIFIED. Root owns compilation and deep audits. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The ACTUAL quotient sheaf on the ACTUAL affine open has finite sections
for the ORIGINAL pi-induced K action. Only natural dimension <=1 is supplied. -/
theorem perfectField_genericNormalizationQuotientSheaf_affineSections_finite_over_ground
    {K : Type u} [Field K] [PerfectField K]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [Ring.DimensionLEOne Γ(X, U)] :
    Module.Finite K
      (SchemeModuleOpenSectionsOver pi (genericNormalizationQuotientSheaf X) U) := by
  let A := Γ(X, U)
  let F := X.functionField
  let beta : K →+* A :=
    (pi.appLE ⊤ U (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  letI : Algebra K A := beta.toAlgebra
  have hbeta : beta.FiniteType := RingHom.FiniteType.comp
    (pi.finiteType_appLE (isAffineOpen_top _) hU (by simp))
    (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  letI : Algebra.FiniteType K A := hbeta
  letI : IsFractionRing A F := functionField_isFractionRing_of_isAffineOpen X U hU
  letI : Module.Finite A (integralClosure A (FractionRing A)) :=
    finiteNormalization_of_finiteType_perfectField K A
  letI : Module.Finite A (integralClosure A F) :=
    Module.Finite.equiv (FractionRing.algEquiv (A := A) F).mapIntegralClosure.toLinearEquiv
  letI : Module.Finite A (localNormalizationDefect A F) := inferInstance
  let D := (ModuleCat.restrictScalars beta).obj (ModuleCat.of A (localNormalizationDefect A F))
  letI : Module.Finite A D :=
    (inferInstance : Module.Finite A (localNormalizationDefect A F))
  letI : IsScalarTower K A D := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  letI : Module.Finite K D := finiteTorsion_finite_over_ground K A D
    (localNormalizationDefect_isTorsion A F)
  let e := genericNormalizationQuotientSheaf_groundAffineSectionsIso K X pi U hU
  have hfinite : Module.Finite K
      ((ModuleCat.restrictScalars beta).obj
        ((schemeOpenModuleFunctor X U).obj (genericNormalizationQuotientSheaf X))) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  exact hfinite

/-- The ACTUAL quotient sheaf restricted to the ACTUAL affine open has finite
native nonzero-stalk support; finite normalization and torsion are derived. -/
theorem perfectField_genericNormalizationQuotientSheaf_affineStalkSupport_finite
    {K : Type u} [Field K] [PerfectField K]
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U]
    [Ring.DimensionLEOne Γ(X, U)] :
    (schemeModuleStalkSupport
      ((Scheme.Modules.restrictFunctor U.ι).obj (genericNormalizationQuotientSheaf X))).Finite := by
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
  have hP : (schemeModuleStalkSupport P).Finite := by
    rw [schemeModuleStalkSupport_eq_of_iso
      (asIso (Scheme.Modules.fromTildeΓ (R := A) P)).symm,
      tilde_actualStalkSupport_eq]
    change (Module.support A (G.obj P)).Finite
    rw [moduleSupport_eq_of_linearEquiv eSections.toLinearEquiv]
    letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
    letI : Module.Finite A (integralClosure A (FractionRing A)) :=
      finiteNormalization_of_finiteType_perfectField K A
    letI : Module.Finite A (integralClosure A X.functionField) :=
      Module.Finite.equiv
        (FractionRing.algEquiv (A := A) X.functionField).mapIntegralClosure.toLinearEquiv
    letI : Module.Finite A (localNormalizationDefect A X.functionField) := inferInstance
    exact finiteTorsion_support_finite A (localNormalizationDefect A X.functionField)
      (localNormalizationDefect_isTorsion A X.functionField)
  have hMU : schemeModuleStalkSupport
      ((Scheme.Modules.restrictFunctor e.hom).obj P) = schemeModuleStalkSupport MU :=
    schemeModuleStalkSupport_eq_of_iso
      ((Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app MU)
  change (schemeModuleStalkSupport MU).Finite
  rw [← hMU, schemeModuleStalkSupport_restrict]
  exact hP.preimage e.hom.homeomorph.injective.injOn

end PfaffianDescent.Coray
