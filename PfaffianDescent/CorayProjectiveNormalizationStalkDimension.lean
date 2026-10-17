import PfaffianDescent.CorayProjectiveIntersectionChartDimension
import PfaffianDescent.CorayGenericNormalizationStalkNormality
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! Actual canonical normalization stalks of the literal projective intersection.
Finite normalization, chart dimension, normality and DVR are conclusions.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
open scoped nonZeroDivisors
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual finite normalization and actual finite type over a characteristic-zero
field construct actual local Noetherianity of the canonical normalized scheme. -/
theorem integralGenericNormalization_isLocallyNoetherian
    {K : Type u} [Field K] [CharZero K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    IsLocallyNoetherian (X.fromSpecStalk (genericPoint X)).normalization := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization :=
    integralScheme_genericNormalization_isFinite X pi
  exact LocallyOfFiniteType.isLocallyNoetherian
    ((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ pi)

/-- Actual stalk Noetherianity, with no assumed finite-normalization certificate. -/
theorem integralGenericNormalization_stalk_isNoetherianRing
    {K : Type u} [Field K] [CharZero K] (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    ∀ y : (X.fromSpecStalk (genericPoint X)).normalization,
      IsNoetherianRing ((X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk y) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI := integralGenericNormalization_isLocallyNoetherian X pi
  intro y
  infer_instance

/-- A nongeneric point of an actual integral scheme has a stalk that is not a
field. This is derived from actual stalk dimension/coheight, not a DVR premise. -/
theorem integralScheme_nongeneric_stalk_not_isField
    (X : Scheme.{u}) [IsIntegral X] (x : X) (hx : x ≠ genericPoint X) :
    ¬ IsField (X.presheaf.stalk x) := by
  intro hfield
  have hz : Order.coheight x = 0 := by
    apply WithBot.coe_injective
    simpa using (ringKrullDim_stalk_eq_coheight x).symm.trans
      (ringKrullDim_eq_zero_of_isField hfield)
  have hstrict : x < genericPoint X := by
    change genericPoint X ⤳ x ∧ ¬ x ⤳ genericPoint X
    refine ⟨genericPoint_specializes x, ?_⟩
    intro hxspec
    exact hx (hxspec.antisymm (genericPoint_specializes x)).eq
  have hpos : 0 < Order.coheight x :=
    Order.coheight_pos_of_lt_top hstrict
  exact hpos.ne' hz

/-- Every actual normalization stalk of the selected integral projective curve
has dimension at most one. Around its actual image point, choose an ORIGINAL
coordinate chart, identify its actual sections, then use actual integral closure
and actual stalk localization. No every-affine dimension certificate is assumed. -/
theorem projectiveIntersection_genericNormalization_stalk_dimensionLEOne
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    ∀ y : (X.fromSpecStalk (genericPoint X)).normalization,
      Ring.DimensionLEOne ((X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk y) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let f := X.fromSpecStalk (genericPoint X)
  change ∀ y : f.normalization,
    Ring.DimensionLEOne (f.normalization.presheaf.stalk y)
  intro y
  obtain ⟨j, z, hz⟩ := exists_coordinate_chart I (f.fromNormalization y)
  let U := (chartι I j).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange (chartι I j)
  have hyU : f.fromNormalization y ∈ U := ⟨z, hz⟩
  letI : Nonempty U := ⟨⟨f.fromNormalization y, hyU⟩⟩
  let e : Γ(X, U) ≃+* ChartRing I j :=
    ((IsOpenImmersion.ΓIsoTop (chartι I j)).symm ≪≫
      Scheme.ΓSpecIso (CommRingCat.of (ChartRing I j))).commRingCatIsoToRingEquiv
  have hdim : ringKrullDim Γ(X, U) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv e]
    exact projectiveIntersection_chart_ringKrullDim_le_one p q hp hp0 n hq hnot j
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

/-- Actual characteristic-zero selected integral projective curve normalization
has DVR stalks at EVERY nongeneric point, hence in particular at nongeneric
closed points. All Noetherianity, dimension and integral closedness are derived. -/
theorem projectiveIntersection_genericNormalization_nongeneric_stalk_isDVR
    {K : Type u} [Field K] [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    ∀ y : (X.fromSpecStalk (genericPoint X)).normalization,
      y ≠ genericPoint (X.fromSpecStalk (genericPoint X)).normalization →
      IsDiscreteValuationRing ((X.fromSpecStalk (genericPoint X)).normalization.presheaf.stalk y) := by
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let Y := (X.fromSpecStalk (genericPoint X)).normalization
  change ∀ y : Y, y ≠ genericPoint Y → IsDiscreteValuationRing (Y.presheaf.stalk y)
  intro y hy
  let R := Y.presheaf.stalk y
  letI : IsNoetherianRing R := integralGenericNormalization_stalk_isNoetherianRing X
    (toBase (projectiveIntersectionIdeal p q hp hq)) y
  letI : Ring.DimensionLEOne R :=
    projectiveIntersection_genericNormalization_stalk_dimensionLEOne p q hp hp0 n hq hnot y
  letI : IsIntegrallyClosed R := integralGenericNormalization_stalk_isIntegrallyClosed X y
  letI : IsDedekindDomain R :=
    (isDedekindDomain_iff R (FractionRing R)).mpr
      ⟨inferInstance, inferInstance, inferInstance,
        fun {_} => (isIntegrallyClosed_iff (FractionRing R)).mp inferInstance⟩
  have hnot : ¬ IsField R := integralScheme_nongeneric_stalk_not_isField Y y hy
  have hdvr : IsDedekindDomain R ↔ IsDiscreteValuationRing R :=
    (IsDiscreteValuationRing.TFAE R hnot).out 2 0 (by rfl) (by rfl)
  exact hdvr.mp inferInstance

end PfaffianDescent.Coray
