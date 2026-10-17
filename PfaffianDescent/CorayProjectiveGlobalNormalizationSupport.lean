import PfaffianDescent.CorayAffineOpenSpecSections
import PfaffianDescent.CorayActualStalkSupportTransport
import PfaffianDescent.CorayGenericNormalizationQuotientAffineSections
import PfaffianDescent.CorayProjectiveIntersectionChartDimension

/-! ACTUAL canonical global normalization quotient has actual finite support.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- ACTUAL canonical normalization quotient SHEAF restricted to an ACTUAL
nonempty affine curve open has ACTUAL finite nonzero-stalk support. Section
comparison, tilde essential image, finite normalization and torsion are proved,
not supplied. The ordinary affine dim≤1 bound is derived at the endpoint below. -/
theorem genericNormalizationQuotientSheaf_affineStalkSupport_finite
    {K : Type u} [Field K] [CharZero K]
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
    exact finiteTypeCurve_normalizationDefect_support_finite_in_fractionField K A X.functionField
  have hMU : schemeModuleStalkSupport
      ((Scheme.Modules.restrictFunctor e.hom).obj P) = schemeModuleStalkSupport MU :=
    schemeModuleStalkSupport_eq_of_iso
      ((Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app MU)
  change (schemeModuleStalkSupport MU).Finite
  rw [← hMU, schemeModuleStalkSupport_restrict]
  exact hP.preimage e.hom.homeomorph.injective.injOn

/-- The ACTUAL canonical GLOBAL normalization quotient SHEAF of the literal
selected integral projective intersection has ACTUAL finite nonzero-stalk
support. Every chart support, dimension and comparison is DERIVED internally.
No support/comparison/genus certificate occurs in this endpoint. -/
theorem projectiveIntersection_genericNormalizationQuotient_stalkSupport_finite
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    (schemeModuleStalkSupport
      (genericNormalizationQuotientSheaf
        (scheme (projectiveIntersectionIdeal p q hp hq)))).Finite := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  let Q := genericNormalizationQuotientSheaf X
  let V : Fin 4 → X.Opens := fun j => (chartι I j).opensRange
  let Y : Fin 4 → Scheme.{u} := fun j => (V j).toScheme
  let f : ∀ j, Y j ⟶ X := fun j => (V j).ι
  have hcover : ∀ x : X, ∃ j, ∃ y : Y j, f j y = x := by
    intro x
    obtain ⟨j, z, hz⟩ := exists_coordinate_chart I x
    exact ⟨j, ⟨x, z, hz⟩, rfl⟩
  have hcoverUp : ∀ x : X, ∃ j : ULift.{u} (Fin 4), ∃ y : Y j.down,
      f j.down y = x := by
    intro x
    obtain ⟨j, y, hy⟩ := hcover x
    exact ⟨⟨j⟩, y, hy⟩
  apply schemeModuleStalkSupport_finite_of_finite_open_cover Q
    (fun j : ULift.{u} (Fin 4) => Y j.down) (fun j => f j.down) hcoverUp
  intro jUp
  let j := jUp.down
  by_cases hnonempty : Nonempty (V j)
  · letI : Nonempty (V j) := hnonempty
    have hV : IsAffineOpen (V j) := isAffineOpen_opensRange (chartι I j)
    let e : Γ(X, V j) ≃+* ChartRing I j :=
      ((IsOpenImmersion.ΓIsoTop (chartι I j)).symm ≪≫
        Scheme.ΓSpecIso (CommRingCat.of (ChartRing I j))).commRingCatIsoToRingEquiv
    have hdim : ringKrullDim Γ(X, V j) ≤ 1 := by
      rw [ringKrullDim_eq_of_ringEquiv e]
      exact projectiveIntersection_chart_ringKrullDim_le_one p q hp hp0 n hq hnot j
    letI : Ring.KrullDimLE 1 Γ(X, V j) := Ring.krullDimLE_iff.mpr hdim
    letI : Ring.DimensionLEOne Γ(X, V j) :=
      ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
    exact genericNormalizationQuotientSheaf_affineStalkSupport_finite X pi (V j) hV
  · have hempty : schemeModuleStalkSupport
        ((Scheme.Modules.restrictFunctor (f j)).obj Q) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hnonempty ⟨y⟩
    rw [hempty]
    exact Set.finite_empty

end PfaffianDescent.Coray
