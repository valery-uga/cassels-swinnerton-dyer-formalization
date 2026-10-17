import PfaffianDescent.QuarticTwistedCubicVeronese
import PfaffianDescent.QuarticExceptionalResidual
import PfaffianDescent.QuarticHomogeneousJets

/-!
# The projective length of the exceptional twisted-cubic intersection

The exceptional base curve in the `Δ = 0` branch is an invertible linear
coordinate image of the standard twisted cubic.  This file transports the
explicit graded-coordinate calculation to its actual projective intersection
with a cubic.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K]

/-- The actual projective intersection of the three exceptional base-locus
quadrics with a homogeneous cubic. -/
noncomputable def exceptionalTwistedCubicCubicIntersectionIdeal
    (a b c d e f : K) (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
  ⟨Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) ⊔
      Ideal.span {F}, by
    rw [← Ideal.span_union]
    apply Ideal.homogeneous_span
    intro q hq
    rcases hq with hq | hq
    · obtain ⟨i, rfl⟩ := hq
      exact ⟨2, scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f i⟩
    · obtain rfl := Set.mem_singleton_iff.mp hq
      exact ⟨3, hF⟩⟩

/-- The exceptional intersection is exactly the existing projective
three-quadric--cubic intersection for the displayed base-locus quadrics. -/
theorem exceptionalTwistedCubicCubicIntersectionIdeal_eq_jetQuadricCubicIntersectionIdeal
    (a b c d e f : K) (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF =
      jetQuadricCubicIntersectionIdeal (scaledBaseLocusQuadricPolynomials a b c d e f)
        (scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f) F hF := by
  apply HomogeneousIdeal.ext
  rfl

/-- Any homogeneous three-quadric net whose ideal is the exceptional
parametrization kernel defines the same cubic intersection as the displayed
exceptional base-locus quadrics. -/
theorem jetQuadricCubicIntersectionIdeal_eq_exceptional_of_ideal_eq_param_ker
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (hQideal : Ideal.span (Set.range Q) =
      RingHom.ker (exceptionalTwistedCubicParam a b c d e).toRingHom)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    jetQuadricCubicIntersectionIdeal Q hQ F hF =
      exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF := by
  apply HomogeneousIdeal.ext
  change Ideal.span (Set.range Q) ⊔ Ideal.span {F} =
    Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) ⊔ Ideal.span {F}
  rw [hQideal, exceptionalTwistedCubic_ideal_eq_param_ker
    a b c d e f ha hb hc hd he hdelta]

/-- The exceptional parametrization on the degree-`n` homogeneous component. -/
noncomputable def exceptionalTwistedCubicParamDegreeMap
    (a b c d e : K) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 4) K n →ₗ[K]
      MvPolynomial.homogeneousSubmodule (Fin 2) K (3 * n) where
  toFun p := ⟨exceptionalTwistedCubicParam a b c d e p.val,
    exceptionalTwistedCubicParam_homogeneous a b c d e p.property⟩
  map_add' p q := by
    apply Subtype.ext
    exact map_add _ _ _
  map_smul' r p := by
    apply Subtype.ext
    exact map_smul _ _ _

/-- An invertible coordinate change preserves the surjectivity of the cubic
Veronese restriction in every homogeneous degree. -/
theorem exceptionalTwistedCubicParamDegreeMap_surjective
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0) (n : ℕ) :
    Function.Surjective (exceptionalTwistedCubicParamDegreeMap a b c d e n) := by
  let M := baseLocusCubicCoefficientMatrix a b c d e
  have hbe : b * e - c * d ≠ 0 :=
    baseLocus_be_sub_cd_ne_zero_of_delta_zero a b c d e f hb hc hd he hdelta
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr
    (baseLocusCubicCoefficientMatrix_det_ne_zero a b c d e ha hb hc hd he hbe)
  intro q
  obtain ⟨r, hr⟩ := standardTwistedCubicParamDegreeMap_surjective (K := K) n q
  let p : MvPolynomial.homogeneousSubmodule (Fin 4) K n :=
    ⟨linearSubstitution M⁻¹ r.val, linearSubstitution_homogeneous M⁻¹ r.property⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  change exceptionalTwistedCubicParam a b c d e (linearSubstitution M⁻¹ r.val) = q.val
  rw [exceptionalTwistedCubicParam_eq_coordinate_change, AlgHom.comp_apply]
  have hcomp : linearSubstitution M (linearSubstitution M⁻¹ r.val) = r.val := by
    change ((linearSubstitution M).comp (linearSubstitution M⁻¹) :
      MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 4) K) r.val = r.val
    rw [linearSubstitution_comp, Matrix.nonsing_inv_mul M hM, linearSubstitution_one]
    rfl
  rw [hcomp]
  exact congrArg Subtype.val hr

/-- In the exceptional branch the defining ideal of the actual projective
intersection is the parametrization kernel together with the cubic. -/
theorem exceptionalTwistedCubicCubicIntersectionIdeal_toIdeal_eq
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF).toIdeal =
      RingHom.ker (exceptionalTwistedCubicParam a b c d e).toRingHom ⊔ Ideal.span {F} := by
  change Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) ⊔
      Ideal.span {F} = _
  rw [exceptionalTwistedCubic_ideal_eq_param_ker a b c d e f ha hb hc hd he hdelta]

/-- Projection from degree-`n` forms to the homogeneous coordinate component
of the exceptional cubic intersection. -/
noncomputable def exceptionalTwistedCubicCubicIntersectionProjection
    (a b c d e f : K) (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 4) K n →ₗ[K]
      CoordinateRing (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) :=
  (Ideal.Quotient.mkₐ K
    (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF).toIdeal).toLinearMap.comp
      (MvPolynomial.homogeneousSubmodule (Fin 4) K n).subtype

lemma exceptionalTwistedCubicCubicIntersectionProjection_range
    (a b c d e f : K) (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (n : ℕ) :
    LinearMap.range (exceptionalTwistedCubicCubicIntersectionProjection a b c d e f F hF n) =
      grading (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) n := by
  rw [exceptionalTwistedCubicCubicIntersectionProjection, LinearMap.range_comp,
    Submodule.range_subtype]
  rfl

/- The projective intersection ideal is killed by restriction to the
exceptional parametrization followed by quotienting by the restricted cubic. -/
theorem exceptionalTwistedCubicCubicIntersectionIdeal_le_projection_ker
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF).toIdeal ≤
      RingHom.ker ((Ideal.Quotient.mkₐ K
        (equationIdeal (exceptionalTwistedCubicParam a b c d e F)
          (exceptionalTwistedCubicParam_homogeneous a b c d e hF)).toIdeal).comp
        (exceptionalTwistedCubicParam a b c d e)).toRingHom := by
  rw [exceptionalTwistedCubicCubicIntersectionIdeal_toIdeal_eq
      a b c d e f ha hb hc hd he hdelta F hF]
  apply sup_le
  · intro p hp
    change Ideal.Quotient.mk (equationIdeal (exceptionalTwistedCubicParam a b c d e F)
      (exceptionalTwistedCubicParam_homogeneous a b c d e hF)).toIdeal
        (exceptionalTwistedCubicParam a b c d e p) = 0
    change exceptionalTwistedCubicParam a b c d e p = 0 at hp
    rw [hp]
    exact map_zero _
  · apply Ideal.span_le.2
    rintro p rfl
    change Ideal.Quotient.mk (equationIdeal (exceptionalTwistedCubicParam a b c d e p)
      (exceptionalTwistedCubicParam_homogeneous a b c d e hF)).toIdeal
        (exceptionalTwistedCubicParam a b c d e p) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))

/-- The quotient map induced by the exceptional parametrization after the
cubic relation is imposed. -/
noncomputable def exceptionalTwistedCubicCubicQuotientMap
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    CoordinateRing (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) →ₐ[K]
      CoordinateRing (equationIdeal (exceptionalTwistedCubicParam a b c d e F)
        (exceptionalTwistedCubicParam_homogeneous a b c d e hF)) :=
  Ideal.Quotient.liftₐ (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF).toIdeal
    ((Ideal.Quotient.mkₐ K (equationIdeal (exceptionalTwistedCubicParam a b c d e F)
      (exceptionalTwistedCubicParam_homogeneous a b c d e hF)).toIdeal).comp
      (exceptionalTwistedCubicParam a b c d e))
    (fun p hp => exceptionalTwistedCubicCubicIntersectionIdeal_le_projection_ker
      a b c d e f ha hb hc hd he hdelta F hF hp)

theorem exceptionalTwistedCubicCubicQuotientMap_mk
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) :
    exceptionalTwistedCubicCubicQuotientMap a b c d e f ha hb hc hd he hdelta F hF
  (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (exceptionalTwistedCubicParam a b c d e p) := rfl

/-- Restriction to the exceptional cubic after quotienting by the cubic
equation. -/
noncomputable def exceptionalTwistedCubicCubicProjection
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (n : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 4) K n →ₗ[K]
      grading (equationIdeal (exceptionalTwistedCubicParam a b c d e F)
        (exceptionalTwistedCubicParam_homogeneous a b c d e hF)) (3 * n) :=
  (((binaryProjectiveProjection (exceptionalTwistedCubicParam a b c d e F)
      (exceptionalTwistedCubicParam_homogeneous a b c d e hF) (3 * n)).codRestrict _
      (fun p => by
        rw [← binaryProjectiveProjection_range]
        exact ⟨p, rfl⟩)).comp
    (exceptionalTwistedCubicParamDegreeMap a b c d e n))

/-- Every homogeneous binary quotient class has a degree-compatible lift
through the exceptional parametrization. -/
theorem exceptionalTwistedCubicCubicProjection_surjective
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (n : ℕ) :
    Function.Surjective (exceptionalTwistedCubicCubicProjection
      a b c d e f ha hb hc hd he hdelta F hF n) := by
  intro y
  have hy : y.val ∈ LinearMap.range
      (binaryProjectiveProjection (exceptionalTwistedCubicParam a b c d e F)
        (exceptionalTwistedCubicParam_homogeneous a b c d e hF) (3 * n)) := by
    rw [binaryProjectiveProjection_range]
    exact y.property
  obtain ⟨q, hq⟩ := hy
  obtain ⟨p, hp⟩ := exceptionalTwistedCubicParamDegreeMap_surjective
    a b c d e f ha hb hc hd he hdelta n q
  refine ⟨p, Subtype.ext ?_⟩
  change binaryProjectiveProjection (exceptionalTwistedCubicParam a b c d e F)
      (exceptionalTwistedCubicParam_homogeneous a b c d e hF) (3 * n)
      (exceptionalTwistedCubicParamDegreeMap a b c d e n p) = y.val
  rw [hp]
  exact hq

/-- Forms in the exceptional intersection ideal restrict to zero in the
binary cubic quotient. -/
theorem exceptionalTwistedCubicCubicProjection_eq_zero_of_mem
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin 4) K n)
    (hp : p.val ∈ (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF).toIdeal) :
    exceptionalTwistedCubicCubicProjection a b c d e f ha hb hc hd he hdelta F hF n p = 0 := by
  apply Subtype.ext
  have hzero := exceptionalTwistedCubicCubicIntersectionIdeal_le_projection_ker
    a b c d e f ha hb hc hd he hdelta F hF hp
  change Ideal.Quotient.mk (equationIdeal (exceptionalTwistedCubicParam a b c d e F)
      (exceptionalTwistedCubicParam_homogeneous a b c d e hF)).toIdeal
        (exceptionalTwistedCubicParam a b c d e p.val) = 0 at hzero
  exact hzero

/-- The degree-wise map from the actual exceptional intersection to its
binary parametrized intersection. -/
noncomputable def exceptionalTwistedCubicCubicComparisonMap
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (n : ℕ) :
    grading (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) n →ₗ[K]
      grading (equationIdeal (exceptionalTwistedCubicParam a b c d e F)
        (exceptionalTwistedCubicParam_homogeneous a b c d e hF)) (3 * n) :=
  ((exceptionalTwistedCubicCubicQuotientMap a b c d e f ha hb hc hd he hdelta F hF).toLinearMap.domRestrict _).codRestrict _ (fun y => by
      obtain ⟨p, hp, hpy⟩ := y.property
      change exceptionalTwistedCubicCubicQuotientMap
        a b c d e f ha hb hc hd he hdelta F hF y.val ∈ _
      rw [← hpy]
      change exceptionalTwistedCubicCubicQuotientMap
        a b c d e f ha hb hc hd he hdelta F hF
          (Ideal.Quotient.mk (exceptionalTwistedCubicCubicIntersectionIdeal
            a b c d e f F hF).toIdeal p) ∈ _
      rw [exceptionalTwistedCubicCubicQuotientMap_mk]
      exact ⟨exceptionalTwistedCubicParam a b c d e p,
        exceptionalTwistedCubicParam_homogeneous a b c d e hp, rfl⟩)

theorem exceptionalTwistedCubicCubicComparisonMap_projection
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin 4) K n) :
    exceptionalTwistedCubicCubicComparisonMap a b c d e f ha hb hc hd he hdelta F hF n
      ⟨exceptionalTwistedCubicCubicIntersectionProjection a b c d e f F hF n p,
        (show exceptionalTwistedCubicCubicIntersectionProjection a b c d e f F hF n p ∈
          grading (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) n by
          rw [← exceptionalTwistedCubicCubicIntersectionProjection_range]
          exact ⟨p, rfl⟩)⟩ =
      exceptionalTwistedCubicCubicProjection a b c d e f ha hb hc hd he hdelta F hF n p := by
  apply Subtype.ext
  rfl

/-- The actual projective exceptional intersection maps onto the binary
intersection in every homogeneous degree. -/
theorem exceptionalTwistedCubicCubicComparisonMap_surjective
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (n : ℕ) :
    Function.Surjective (exceptionalTwistedCubicCubicComparisonMap
      a b c d e f ha hb hc hd he hdelta F hF n) := by
  intro y
  obtain ⟨p, hp⟩ := exceptionalTwistedCubicCubicProjection_surjective
    a b c d e f ha hb hc hd he hdelta F hF n y
  let z : grading (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) n :=
    ⟨exceptionalTwistedCubicCubicIntersectionProjection a b c d e f F hF n p,
      (show exceptionalTwistedCubicCubicIntersectionProjection a b c d e f F hF n p ∈
        grading (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) n by
        rw [← exceptionalTwistedCubicCubicIntersectionProjection_range]
        exact ⟨p, rfl⟩)⟩
  refine ⟨z, ?_⟩
  simpa only [z] using
    (exceptionalTwistedCubicCubicComparisonMap_projection
      a b c d e f ha hb hc hd he hdelta F hF n p).trans hp

/-- In degree at least three, a form whose exceptional parametrized class
vanishes belongs to the actual quadric--cubic intersection ideal. -/
theorem mem_exceptionalTwistedCubicCubicIntersectionIdeal_of_projection_eq_zero
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : exceptionalTwistedCubicParam a b c d e F ≠ 0)
    (n : ℕ) (hn : 3 ≤ n)
    (p : MvPolynomial.homogeneousSubmodule (Fin 4) K n)
    (hp : exceptionalTwistedCubicCubicProjection
      a b c d e f ha hb hc hd he hdelta F hF n p = 0) :
    p.val ∈ (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF).toIdeal := by
  have hp' := congrArg Subtype.val hp
  change Ideal.Quotient.mk (equationIdeal (exceptionalTwistedCubicParam a b c d e F)
      (exceptionalTwistedCubicParam_homogeneous a b c d e hF)).toIdeal
        (exceptionalTwistedCubicParam a b c d e p.val) = 0 at hp'
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hp'
  change exceptionalTwistedCubicParam a b c d e p.val ∈
    Ideal.span ({exceptionalTwistedCubicParam a b c d e F} : Set (MvPolynomial (Fin 2) K)) at hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hqP : q * exceptionalTwistedCubicParam a b c d e F =
      exceptionalTwistedCubicParam a b c d e p.val := by
    rw [mul_comm]
    exact hq.symm
  have hqhom : q.IsHomogeneous (3 * (n - 3)) := by
    apply homogeneous_of_mul_right (exceptionalTwistedCubicParam_homogeneous a b c d e hF)
      hnonzero
    rw [show 3 * (n - 3) + 9 = 3 * n by omega, hqP]
    exact exceptionalTwistedCubicParam_homogeneous a b c d e p.property
  obtain ⟨r, hr⟩ := exceptionalTwistedCubicParamDegreeMap_surjective
    a b c d e f ha hb hc hd he hdelta (n - 3) ⟨q, hqhom⟩
  have hrval : exceptionalTwistedCubicParam a b c d e r.val = q := congrArg Subtype.val hr
  have hzero : exceptionalTwistedCubicParam a b c d e (p.val - F * r.val) = 0 := by
    rw [map_sub, map_mul, hrval, ← hqP]
    ring
  have hbase : p.val - F * r.val ∈
      Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) := by
    rw [exceptionalTwistedCubic_ideal_eq_param_ker
      a b c d e f ha hb hc hd he hdelta]
    exact hzero
  change p.val ∈ Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) ⊔
    Ideal.span {F}
  rw [show p.val = (p.val - F * r.val) + F * r.val by ring]
  apply add_mem
  · exact (le_sup_left : Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) ≤
      Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) ⊔
        Ideal.span {F}) hbase
  · apply (le_sup_right : Ideal.span {F} ≤
      Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) ⊔
        Ideal.span {F})
    rw [mul_comm]
    exact Ideal.mul_mem_left (Ideal.span {F}) r.val
      (Ideal.subset_span (Set.mem_singleton F))

theorem exceptionalTwistedCubicCubicComparisonMap_injective
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : exceptionalTwistedCubicParam a b c d e F ≠ 0)
    (n : ℕ) (hn : 3 ≤ n) :
    Function.Injective (exceptionalTwistedCubicCubicComparisonMap
      a b c d e f ha hb hc hd he hdelta F hF n) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro y hy
  obtain ⟨p, hp, hpy⟩ := y.property
  let z : grading (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) n :=
    ⟨exceptionalTwistedCubicCubicIntersectionProjection a b c d e f F hF n ⟨p, hp⟩,
      (show Ideal.Quotient.mk (exceptionalTwistedCubicCubicIntersectionIdeal
        a b c d e f F hF).toIdeal p ∈
          grading (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) n by
        exact ⟨p, hp, rfl⟩)⟩
  have hzy : z = y := by
    apply Subtype.ext
    exact hpy
  have hcompz : exceptionalTwistedCubicCubicComparisonMap
      a b c d e f ha hb hc hd he hdelta F hF n z = 0 := by
    rw [hzy]
    exact hy
  have hprojection : exceptionalTwistedCubicCubicProjection
      a b c d e f ha hb hc hd he hdelta F hF n ⟨p, hp⟩ = 0 := by
    exact (exceptionalTwistedCubicCubicComparisonMap_projection
      a b c d e f ha hb hc hd he hdelta F hF n ⟨p, hp⟩).symm.trans hcompz
  have hmem := mem_exceptionalTwistedCubicCubicIntersectionIdeal_of_projection_eq_zero
    a b c d e f ha hb hc hd he hdelta F hF hnonzero n hn ⟨p, hp⟩ hprojection
  apply Subtype.ext
  rw [← hpy]
  change Ideal.Quotient.mk (exceptionalTwistedCubicCubicIntersectionIdeal
    a b c d e f F hF).toIdeal p = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

theorem exceptionalTwistedCubicCubicComparisonMap_bijective
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : exceptionalTwistedCubicParam a b c d e F ≠ 0)
    (n : ℕ) (hn : 3 ≤ n) :
    Function.Bijective (exceptionalTwistedCubicCubicComparisonMap
      a b c d e f ha hb hc hd he hdelta F hF n) :=
  ⟨exceptionalTwistedCubicCubicComparisonMap_injective
      a b c d e f ha hb hc hd he hdelta F hF hnonzero n hn,
    exceptionalTwistedCubicCubicComparisonMap_surjective
      a b c d e f ha hb hc hd he hdelta F hF n⟩

/-- The actual exceptional twisted-cubic--cubic intersection has homogeneous
coordinate dimension nine from degree three onward. -/
theorem exceptionalTwistedCubicCubicIntersection_grade_finrank
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : exceptionalTwistedCubicParam a b c d e F ≠ 0)
    (n : ℕ) (hn : 3 ≤ n) :
    Module.finrank K (grading
      (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) n) = 9 := by
  let E := LinearEquiv.ofBijective
    (exceptionalTwistedCubicCubicComparisonMap
      a b c d e f ha hb hc hd he hdelta F hF n)
    (exceptionalTwistedCubicCubicComparisonMap_bijective
      a b c d e f ha hb hc hd he hdelta F hF hnonzero n hn)
  calc
    Module.finrank K (grading
        (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) n) =
        Module.finrank K (grading
          (equationIdeal (exceptionalTwistedCubicParam a b c d e F)
            (exceptionalTwistedCubicParam_homogeneous a b c d e hF)) (3 * n)) := E.finrank_eq
    _ = 9 := by
      have hbinary := binary_projective_grade_finrank (exceptionalTwistedCubicParam a b c d e F)
        (exceptionalTwistedCubicParam_homogeneous a b c d e hF) hnonzero (3 * (n - 3))
      have hdegree : 3 * (n - 3) + 9 = 3 * n := by omega
      rw [hdegree] at hbinary
      exact hbinary

theorem exceptionalTwistedCubicCubicIntersection_isFinite [Infinite K]
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : exceptionalTwistedCubicParam a b c d e F ≠ 0) :
    IsFinite (toBase (exceptionalTwistedCubicCubicIntersectionIdeal
      a b c d e f F hF)) := by
  apply projective_finite_of_hilbert_bound
    (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) 3 9
  intro n hn
  exact (exceptionalTwistedCubicCubicIntersection_grade_finrank
    a b c d e f ha hb hc hd he hdelta F hF hnonzero n hn).le

theorem exceptionalTwistedCubicCubicIntersection_finiteSchemeRank [Infinite K]
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : exceptionalTwistedCubicParam a b c d e F ≠ 0)
    [IsFinite (toBase (exceptionalTwistedCubicCubicIntersectionIdeal
      a b c d e f F hF))] :
    AllCharacteristics.finiteSchemeRank (toBase
      (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF)) = 9 := by
  apply projective_length_of_eventual_hilbert
    (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) 3 9
  intro n hn
  exact exceptionalTwistedCubicCubicIntersection_grade_finrank
    a b c d e f ha hb hc hd he hdelta F hF hnonzero n hn



/-- Replacing a homogeneous projective ideal by an equal one preserves the
finite rank of its structure morphism. -/
theorem finiteSchemeRank_toBase_of_homogeneousIdeal_eq
    (I J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hIJ : I = J) [IsFinite (toBase I)] [IsFinite (toBase J)] :
    AllCharacteristics.finiteSchemeRank (toBase I) =
      AllCharacteristics.finiteSchemeRank (toBase J) := by
  subst J
  rfl

/-- The rank-nine calculation applies directly to any three-quadric
intersection whose ideal is the exceptional parametrization kernel. -/
theorem jetQuadricCubicIntersection_exceptional_finiteSchemeRank [Infinite K]
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0)
    (Q : Fin 3 → MvPolynomial (Fin 4) K)
    (hQ : ∀ i, (Q i).IsHomogeneous 2)
    (hQideal : Ideal.span (Set.range Q) =
      RingHom.ker (exceptionalTwistedCubicParam a b c d e).toRingHom)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : exceptionalTwistedCubicParam a b c d e F ≠ 0) :
    ∃ hfinite : IsFinite (toBase (jetQuadricCubicIntersectionIdeal Q hQ F hF)),
      @AllCharacteristics.finiteSchemeRank K _ _
        (toBase (jetQuadricCubicIntersectionIdeal Q hQ F hF)) hfinite = 9 := by
  have hI := jetQuadricCubicIntersectionIdeal_eq_exceptional_of_ideal_eq_param_ker
    a b c d e f ha hb hc hd he hdelta Q hQ hQideal F hF
  let hfiniteExceptional : IsFinite (toBase
      (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF)) :=
    exceptionalTwistedCubicCubicIntersection_isFinite
      a b c d e f ha hb hc hd he hdelta F hF hnonzero
  letI : IsFinite (toBase
      (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF)) := hfiniteExceptional
  let hfinite : IsFinite (toBase (jetQuadricCubicIntersectionIdeal Q hQ F hF)) := by
    rw [hI]
    exact hfiniteExceptional
  letI : IsFinite (toBase (jetQuadricCubicIntersectionIdeal Q hQ F hF)) := hfinite
  refine ⟨hfinite, ?_⟩
  exact (finiteSchemeRank_toBase_of_homogeneousIdeal_eq
    (jetQuadricCubicIntersectionIdeal Q hQ F hF)
    (exceptionalTwistedCubicCubicIntersectionIdeal a b c d e f F hF) hI).trans
      (exceptionalTwistedCubicCubicIntersection_finiteSchemeRank
        a b c d e f ha hb hc hd he hdelta F hF hnonzero)

end QuarticNet
end PfaffianDescent
