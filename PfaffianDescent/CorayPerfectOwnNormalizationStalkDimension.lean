import PfaffianDescent.CorayHomogeneousPrimeComponentGeometry
import PfaffianDescent.CorayPerfectFiniteSchemeGenericNormalization
import PfaffianDescent.CorayProjectiveNormalizationStalkDimension

/-! SOURCE ONLY / UNVERIFIED. Actual OWN selected-component normalization
stalk geometry over the original perfect field. No integral whole-intersection,
CharZero, Infinite, genus, duality, Euler, H1 or point-ideal premise. The final
DVR statement is for actual nongeneric points; closed-point nongenericity on a
minimal component remains a separate geometric obligation. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
open scoped nonZeroDivisors
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Native finite perfect-field normalization derives native local Noetherianity.
This uses the SAME canonical generic-point map, not an abstract normal model. -/
theorem perfectField_integralGenericNormalization_isLocallyNoetherian
    {K : Type u} [Field K] [PerfectField K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    IsLocallyNoetherian (X.fromSpecStalk (genericPoint X)).normalization := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization :=
    perfectField_integralScheme_genericNormalization_isFinite X pi
  exact LocallyOfFiniteType.isLocallyNoetherian
    ((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ pi)

/-- Actual OWN normalization stalk dimension comes from the OWN chart quotient,
its genuine integral closure, and the actual affine stalk localization. -/
theorem selectedProjectivePrimeComponent_genericNormalization_stalk_dimensionLEOne
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    ∀ y : (X.fromSpecStalk (genericPoint X)).normalization,
      Ring.DimensionLEOne ((X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk y) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let f := X.fromSpecStalk (genericPoint X)
  change ∀ y : f.normalization,
    Ring.DimensionLEOne (f.normalization.presheaf.stalk y)
  intro y
  obtain ⟨j, z, hz⟩ := exists_coordinate_chart C (f.fromNormalization y)
  let U := (chartι C j).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (chartι C j)
  have hyU : f.fromNormalization y ∈ U := ⟨z, hz⟩
  letI : Nonempty U := ⟨⟨f.fromNormalization y, hyU⟩⟩
  let e : Γ(X, U) ≃+* ChartRing C j :=
    ((IsOpenImmersion.ΓIsoTop (chartι C j)).symm ≪≫
      Scheme.ΓSpecIso (CommRingCat.of (ChartRing C j))).commRingCatIsoToRingEquiv
  have hdim : ringKrullDim Γ(X, U) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e]
    exact selectedProjectiveComponent_chart_ringKrullDim_le_one p q hp hp0 n hq hnot C hIC j
  letI : Ring.KrullDimLE 1 Γ(X, U) := Ring.krullDimLE_iff.mpr hdim
  letI : Ring.DimensionLEOne Γ(X, U) :=
    ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
  let V := f.fromNormalization ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage f.fromNormalization
  have hyV : y ∈ V := hyU
  letI : Ring.DimensionLEOne Γ(f.normalization, V) :=
    Ring.DimensionLEOne.of_ringEquiv
      (integralGenericNormalization_preimageSectionsRingEquiv X U hU)
  letI : IsDomain Γ(f.normalization, V) :=
    integralGenericNormalization_preimageSections_isDomain X U hU
  letI : Algebra Γ(f.normalization, V) (f.normalization.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk f.normalization.presheaf ⟨y, hyV⟩
  let P := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  letI : IsLocalization P.primeCompl (f.normalization.presheaf.stalk y) :=
    hV.isLocalization_stalk ⟨y, hyV⟩
  exact Ring.DimensionLEOne.localization (f.normalization.presheaf.stalk y)
    P.primeCompl_le_nonZeroDivisors

/-- Genuine OWN normalization DVRs at all nongeneric points. Native perfect-field
finiteness, actual component charts and actual normality discharge every local
ring condition. This does not identify a singular original point with a divisor
on its normalization or assume that a normalization closed point is nongeneric. -/
theorem perfectField_selectedProjectivePrimeComponent_genericNormalization_nongeneric_stalk_isDVR
    {K : Type u} [Field K] [PerfectField K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    ∀ y : (X.fromSpecStalk (genericPoint X)).normalization,
      y ≠ genericPoint (X.fromSpecStalk (genericPoint X)).normalization →
      IsDiscreteValuationRing ((X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk y) := by
  letI : IsIntegral (scheme C) := homogeneousPrime_projectiveScheme_isIntegral C hprime P
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let Y := (X.fromSpecStalk (genericPoint X)).normalization
  letI : IsLocallyNoetherian Y :=
    perfectField_integralGenericNormalization_isLocallyNoetherian X (toBase C)
  change ∀ y : Y, y ≠ genericPoint Y → IsDiscreteValuationRing (Y.presheaf.stalk y)
  intro y hy
  let R := Y.presheaf.stalk y
  letI : IsNoetherianRing R := inferInstance
  letI : Ring.DimensionLEOne R :=
    selectedProjectivePrimeComponent_genericNormalization_stalk_dimensionLEOne
      p q hp hp0 n hq hnot C hIC hprime P y
  letI : IsIntegrallyClosed R := integralGenericNormalization_stalk_isIntegrallyClosed X y
  letI : IsDedekindDomain R :=
    (isDedekindDomain_iff R (FractionRing R)).mpr
      ⟨inferInstance, inferInstance, inferInstance,
        fun {_} => (isIntegrallyClosed_iff (FractionRing R)).mp inferInstance⟩
  have hnotField : ¬ IsField R := integralScheme_nongeneric_stalk_not_isField Y y hy
  have hdvr : IsDedekindDomain R ↔ IsDiscreteValuationRing R :=
    (IsDiscreteValuationRing.TFAE R hnotField).out 2 0 (by rfl) (by rfl)
  exact hdvr.mp inferInstance

end PfaffianDescent.Coray
