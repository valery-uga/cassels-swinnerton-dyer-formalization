import PfaffianDescent.QuarticTwistedCubicResidual
import PfaffianDescent.BinaryProjectiveLength

/-!
# Homogeneous lifts for the cubic Veronese parametrization

Every binary monomial of degree `3d` has an explicit homogeneous degree-`d`
lift through the standard twisted-cubic parametrization.  This is the graded
coordinate-ring input for comparing the parameter-space degree-nine
intersection with the projective intersection on the twisted cubic.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K]

/-- The standard twisted-cubic ideal as a homogeneous projective ideal. -/
noncomputable def standardTwistedCubicHomogeneousIdeal :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
  ⟨standardTwistedCubicIdeal K, Ideal.homogeneous_span _ _ (by
    intro q hq
    obtain ⟨i, rfl⟩ := hq
    exact ⟨2, standardTwistedCubicGenerators_homogeneous K i⟩)⟩

/-- The projective scheme-theoretic intersection of the standard twisted
cubic and a cubic form. -/
noncomputable def standardTwistedCubicCubicIntersectionIdeal
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
  standardTwistedCubicHomogeneousIdeal ⊔ equationIdeal F hF

/-- An explicit degree-`d` lift of a binary monomial whose second exponent is
at most `3d`. -/
noncomputable def standardCubicLift (d i : ℕ) (c : K) : MvPolynomial (Fin 4) K :=
  if i % 3 = 0 then C c * X 0 ^ (d - i / 3) * X 3 ^ (i / 3)
  else if i % 3 = 1 then C c * X 0 ^ (d - i / 3 - 1) * X 1 * X 3 ^ (i / 3)
  else C c * X 0 ^ (d - i / 3 - 1) * X 2 * X 3 ^ (i / 3)

/-- The explicit lift has its required homogeneous degree. -/
theorem standardCubicLift_homogeneous {d i : ℕ} (hi : i ≤ 3 * d) (c : K) :
    (standardCubicLift d i c).IsHomogeneous d := by
  have hqle : i / 3 ≤ d := by omega
  unfold standardCubicLift
  split_ifs with h0 h1
  · have h := (isHomogeneous_C (Fin 4) c).mul
      ((isHomogeneous_X_pow 0 (d - i / 3)).mul (isHomogeneous_X_pow 3 (i / 3)))
    simpa only [mul_assoc, zero_add, Nat.sub_add_cancel hqle] using h
  · have hq1 : i / 3 + 1 ≤ d := by omega
    have hdq : d - i / 3 - 1 + 1 + i / 3 = d := by omega
    have h := ((isHomogeneous_C (Fin 4) c).mul
      ((isHomogeneous_X_pow 0 (d - i / 3 - 1)).mul (isHomogeneous_X K 1))).mul
      (isHomogeneous_X_pow 3 (i / 3))
    simpa only [mul_assoc, zero_add, hdq] using h
  · have hmod : i % 3 = 2 := by omega
    have hq1 : i / 3 + 1 ≤ d := by omega
    have hdq : d - i / 3 - 1 + 1 + i / 3 = d := by omega
    have h := ((isHomogeneous_C (Fin 4) c).mul
      ((isHomogeneous_X_pow 0 (d - i / 3 - 1)).mul (isHomogeneous_X K 2))).mul
      (isHomogeneous_X_pow 3 (i / 3))
    simpa only [mul_assoc, zero_add, hdq] using h

/-- The standard parametrization sends the lift of a degree-`3d` binary
monomial back to that monomial. -/
theorem standardTwistedCubicParam_standardCubicLift
    (e : Fin 2 →₀ ℕ) (d : ℕ) (hd : e.degree = 3 * d) (c : K) :
    standardTwistedCubicParam K (standardCubicLift d (e 1) c) = monomial e c := by
  have hdegree : e 0 + e 1 = 3 * d := by
    change e.sum (fun _ n => n) = 3 * d at hd
    rw [Finsupp.sum_fintype e (fun _ n => n) (by simp)] at hd
    simpa [Fin.sum_univ_two] using hd
  have hqle : e 1 / 3 ≤ d := by omega
  have hmono : monomial e c = C c * X 0 ^ (e 0) * X 1 ^ (e 1) := by
    simp [monomial_eq, Finsupp.prod_fintype, Fin.prod_univ_two]
    ring
  rw [hmono]
  unfold standardCubicLift
  split_ifs with h0 h1
  · simp [standardTwistedCubicParam]
    rw [show e 0 = 3 * (d - e 1 / 3) by omega,
      show e 1 = 3 * (e 1 / 3) by omega]
    have hdiv : (3 * (e 1 / 3)) / 3 = e 1 / 3 := by omega
    rw [hdiv]
    ring
  · simp [standardTwistedCubicParam]
    rw [show e 0 = 3 * (d - e 1 / 3 - 1) + 2 by omega,
      show e 1 = 3 * (e 1 / 3) + 1 by omega]
    have hdiv : (3 * (e 1 / 3) + 1) / 3 = e 1 / 3 := by omega
    rw [hdiv]
    ring
  · have hmod : e 1 % 3 = 2 := by omega
    simp [standardTwistedCubicParam]
    rw [show e 0 = 3 * (d - e 1 / 3 - 1) + 1 by omega,
      show e 1 = 3 * (e 1 / 3) + 2 by omega]
    have hdiv : (3 * (e 1 / 3) + 2) / 3 = e 1 / 3 := by omega
    rw [hdiv]
    ring

/-- The degree-`d` component of the standard cubic parametrization. -/
noncomputable def standardTwistedCubicParamDegreeMap (d : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 4) K d →ₗ[K]
      MvPolynomial.homogeneousSubmodule (Fin 2) K (3 * d) :=
  (((standardTwistedCubicParam K).toLinearMap.comp
    (MvPolynomial.homogeneousSubmodule (Fin 4) K d).subtype).codRestrict _
      (fun p => standardTwistedCubicParam_homogeneous p.property))

/-- The cubic Veronese parametrization is surjective on every matching
homogeneous component. -/
theorem standardTwistedCubicParamDegreeMap_surjective (d : ℕ) :
    Function.Surjective (standardTwistedCubicParamDegreeMap (K := K) d) := by
  intro P
  let T : MvPolynomial (Fin 4) K := ∑ e ∈ P.val.support,
    standardCubicLift d (e 1) (coeff e P.val)
  have hT : T.IsHomogeneous d := by
    dsimp [T]
    apply IsHomogeneous.sum
    intro e he
    have hedegree : e.degree = 3 * d := by
      have hone : (1 : Fin 2 → ℕ) = fun _ : Fin 2 => 1 := by
        funext i
        rfl
      rw [Finsupp.degree_eq_weight_one, ← hone]
      exact P.property (mem_support_iff.mp he)
    have hsum : e 0 + e 1 = 3 * d := by
      change e.sum (fun _ n => n) = 3 * d at hedegree
      rw [Finsupp.sum_fintype e (fun _ n => n) (by simp)] at hedegree
      simpa [Fin.sum_univ_two] using hedegree
    apply standardCubicLift_homogeneous
    omega
  refine ⟨⟨T, hT⟩, Subtype.ext ?_⟩
  change standardTwistedCubicParam K T = P.val
  rw [show P.val = ∑ e ∈ P.val.support, monomial e (coeff e P.val) from P.val.as_sum]
  dsimp [T]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hedegree : e.degree = 3 * d := by
    have hone : (1 : Fin 2 → ℕ) = fun _ : Fin 2 => 1 := by
      funext i
      rfl
    rw [Finsupp.degree_eq_weight_one, ← hone]
    exact P.property (mem_support_iff.mp he)
  exact standardTwistedCubicParam_standardCubicLift e d
    hedegree (coeff e P.val)

/-- Restriction along the twisted cubic followed by quotienting by a cubic
form on the curve, in a fixed homogeneous degree. -/
noncomputable def standardTwistedCubicCubicProjection
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (d : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 4) K d →ₗ[K]
      grading (equationIdeal (standardTwistedCubicParam K F)
        (standardTwistedCubicParam_homogeneous hF)) (3 * d) :=
  (((binaryProjectiveProjection (standardTwistedCubicParam K F)
      (standardTwistedCubicParam_homogeneous hF) (3 * d)).codRestrict _
      (fun p => by
        rw [← binaryProjectiveProjection_range]
        exact ⟨p, rfl⟩)).comp
    (standardTwistedCubicParamDegreeMap (K := K) d))

/-- The degree-wise restriction-and-quotient map is onto the corresponding
binary projective quotient component. -/
theorem standardTwistedCubicCubicProjection_surjective
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (d : ℕ) :
    Function.Surjective (standardTwistedCubicCubicProjection F hF d) := by
  intro y
  have hy : y.val ∈ LinearMap.range
      (binaryProjectiveProjection (standardTwistedCubicParam K F)
        (standardTwistedCubicParam_homogeneous hF) (3 * d)) := by
    rw [binaryProjectiveProjection_range]
    exact y.property
  obtain ⟨b, hb⟩ := hy
  obtain ⟨a, ha⟩ := standardTwistedCubicParamDegreeMap_surjective (K := K) d b
  refine ⟨a, Subtype.ext ?_⟩
  change binaryProjectiveProjection (standardTwistedCubicParam K F)
      (standardTwistedCubicParam_homogeneous hF) (3 * d)
      (standardTwistedCubicParamDegreeMap (K := K) d a) = y.val
  rw [ha]
  exact hb

/-- In degrees at least three, the restriction-and-quotient map has
nine-dimensional range when the cubic does not contain the twisted cubic. -/
theorem standardTwistedCubicCubicProjection_range_finrank
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : standardTwistedCubicParam K F ≠ 0)
    (d : ℕ) (hd : 3 ≤ d) :
    Module.finrank K (LinearMap.range
      (standardTwistedCubicCubicProjection F hF d)) = 9 := by
  have hbinary := binary_projective_grade_finrank (standardTwistedCubicParam K F)
    (standardTwistedCubicParam_homogeneous hF) hnonzero (3 * (d - 3))
  have hdegree : 3 * (d - 3) + 9 = 3 * d := by omega
  rw [hdegree] at hbinary
  rw [LinearMap.range_eq_top.mpr
    (standardTwistedCubicCubicProjection_surjective F hF d)]
  simpa using hbinary

/-- The projective intersection ideal is annihilated by restriction to the
twisted cubic followed by quotienting by the restricted cubic. -/
theorem standardTwistedCubicCubicIntersectionIdeal_le_projection_ker
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    (standardTwistedCubicCubicIntersectionIdeal F hF).toIdeal ≤
      RingHom.ker ((Ideal.Quotient.mkₐ K
        (equationIdeal (standardTwistedCubicParam K F)
          (standardTwistedCubicParam_homogeneous hF)).toIdeal).comp
        (standardTwistedCubicParam K)).toRingHom := by
  change standardTwistedCubicIdeal K ⊔ Ideal.span {F} ≤ _
  apply sup_le
  · rw [standardTwistedCubicIdeal_eq_ker]
    intro p hp
    change Ideal.Quotient.mk (equationIdeal (standardTwistedCubicParam K F)
      (standardTwistedCubicParam_homogeneous hF)).toIdeal
        (standardTwistedCubicParam K p) = 0
    change standardTwistedCubicParam K p = 0 at hp
    rw [hp]
    exact map_zero _
  · apply Ideal.span_le.2
    rintro p rfl
    change Ideal.Quotient.mk (equationIdeal (standardTwistedCubicParam K p)
      (standardTwistedCubicParam_homogeneous hF)).toIdeal
        (standardTwistedCubicParam K p) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton _))

/-- Restriction to the twisted cubic descends from the intersection
coordinate ring to the binary coordinate ring cut out by the restricted
cubic. -/
noncomputable def standardTwistedCubicCubicQuotientMap
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) :
    CoordinateRing (standardTwistedCubicCubicIntersectionIdeal F hF) →ₐ[K]
      CoordinateRing (equationIdeal (standardTwistedCubicParam K F)
        (standardTwistedCubicParam_homogeneous hF)) :=
  Ideal.Quotient.liftₐ (standardTwistedCubicCubicIntersectionIdeal F hF).toIdeal
    ((Ideal.Quotient.mkₐ K (equationIdeal (standardTwistedCubicParam K F)
      (standardTwistedCubicParam_homogeneous hF)).toIdeal).comp
      (standardTwistedCubicParam K))
    (fun p hp => standardTwistedCubicCubicIntersectionIdeal_le_projection_ker F hF hp)

/-- On a polynomial representative the descended map is ordinary
parametrization followed by binary quotienting. -/
theorem standardTwistedCubicCubicQuotientMap_mk
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) K) :
    standardTwistedCubicCubicQuotientMap F hF
      (Ideal.Quotient.mk (standardTwistedCubicCubicIntersectionIdeal F hF).toIdeal p) =
        Ideal.Quotient.mk (equationIdeal (standardTwistedCubicParam K F)
          (standardTwistedCubicParam_homogeneous hF)).toIdeal
          (standardTwistedCubicParam K p) := rfl

/-- Every homogeneous equation of the projective intersection is killed by
the degree-wise binary quotient map. -/
theorem standardTwistedCubicCubicProjection_eq_zero_of_mem
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin 4) K d)
    (hp : p.val ∈ (standardTwistedCubicCubicIntersectionIdeal F hF).toIdeal) :
    standardTwistedCubicCubicProjection F hF d p = 0 := by
  apply Subtype.ext
  have hzero := standardTwistedCubicCubicIntersectionIdeal_le_projection_ker F hF hp
  change Ideal.Quotient.mk (equationIdeal (standardTwistedCubicParam K F)
      (standardTwistedCubicParam_homogeneous hF)).toIdeal
        (standardTwistedCubicParam K p.val) = 0 at hzero
  exact hzero

/-- The usual homogeneous projection to the coordinate ring of the actual
twisted-cubic--cubic intersection. -/
noncomputable def standardTwistedCubicCubicIntersectionProjection
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (d : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin 4) K d →ₗ[K]
      CoordinateRing (standardTwistedCubicCubicIntersectionIdeal F hF) :=
  (Ideal.Quotient.mkₐ K (standardTwistedCubicCubicIntersectionIdeal F hF).toIdeal).toLinearMap.comp
    (MvPolynomial.homogeneousSubmodule (Fin 4) K d).subtype

/-- Its range is exactly the degree-`d` projective coordinate component. -/
theorem standardTwistedCubicCubicIntersectionProjection_range
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (d : ℕ) :
    LinearMap.range (standardTwistedCubicCubicIntersectionProjection F hF d) =
      grading (standardTwistedCubicCubicIntersectionIdeal F hF) d := by
  rw [standardTwistedCubicCubicIntersectionProjection, LinearMap.range_comp,
    Submodule.range_subtype]
  rfl

/-- In every degree, restriction maps the homogeneous coordinate component
of the projective intersection to the corresponding binary component. -/
noncomputable def standardTwistedCubicCubicComparisonMap
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (d : ℕ) :
    grading (standardTwistedCubicCubicIntersectionIdeal F hF) d →ₗ[K]
      grading (equationIdeal (standardTwistedCubicParam K F)
        (standardTwistedCubicParam_homogeneous hF)) (3 * d) :=
  ((standardTwistedCubicCubicQuotientMap F hF).toLinearMap.domRestrict _).codRestrict _
    (fun y => by
      obtain ⟨p, hp, hpy⟩ := y.property
      change standardTwistedCubicCubicQuotientMap F hF y.val ∈ _
      rw [← hpy]
      change standardTwistedCubicCubicQuotientMap F hF
        (Ideal.Quotient.mk (standardTwistedCubicCubicIntersectionIdeal F hF).toIdeal p) ∈ _
      rw [standardTwistedCubicCubicQuotientMap_mk]
      exact ⟨standardTwistedCubicParam K p,
        standardTwistedCubicParam_homogeneous hp, rfl⟩)

/-- The comparison sends the class of a homogeneous quaternary form to the
binary class of its parametrized restriction. -/
theorem standardTwistedCubicCubicComparisonMap_projection
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (d : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (Fin 4) K d) :
    standardTwistedCubicCubicComparisonMap F hF d
      ⟨standardTwistedCubicCubicIntersectionProjection F hF d p,
        (show standardTwistedCubicCubicIntersectionProjection F hF d p ∈
          grading (standardTwistedCubicCubicIntersectionIdeal F hF) d by
          rw [← standardTwistedCubicCubicIntersectionProjection_range]
          exact ⟨p, rfl⟩)⟩ =
      standardTwistedCubicCubicProjection F hF d p := by
  apply Subtype.ext
  rfl

/-- The projective homogeneous intersection component maps onto the binary
component in the corresponding triple degree. -/
theorem standardTwistedCubicCubicComparisonMap_surjective
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (d : ℕ) :
    Function.Surjective (standardTwistedCubicCubicComparisonMap F hF d) := by
  intro y
  obtain ⟨p, hp⟩ := standardTwistedCubicCubicProjection_surjective F hF d y
  let z : grading (standardTwistedCubicCubicIntersectionIdeal F hF) d :=
    ⟨standardTwistedCubicCubicIntersectionProjection F hF d p,
      (show standardTwistedCubicCubicIntersectionProjection F hF d p ∈
        grading (standardTwistedCubicCubicIntersectionIdeal F hF) d by
        rw [← standardTwistedCubicCubicIntersectionProjection_range]
        exact ⟨p, rfl⟩)⟩
  refine ⟨z, ?_⟩
  simpa only [z] using
    (standardTwistedCubicCubicComparisonMap_projection F hF d p).trans hp

/-- In degree at least three, every homogeneous form whose restricted binary
class vanishes already belongs to the twisted-cubic--cubic intersection
ideal. -/
theorem mem_standardTwistedCubicCubicIntersectionIdeal_of_projection_eq_zero
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : standardTwistedCubicParam K F ≠ 0)
    (d : ℕ) (hd : 3 ≤ d)
    (p : MvPolynomial.homogeneousSubmodule (Fin 4) K d)
    (hp : standardTwistedCubicCubicProjection F hF d p = 0) :
    p.val ∈ (standardTwistedCubicCubicIntersectionIdeal F hF).toIdeal := by
  have hp' := congrArg Subtype.val hp
  change Ideal.Quotient.mk (equationIdeal (standardTwistedCubicParam K F)
      (standardTwistedCubicParam_homogeneous hF)).toIdeal
        (standardTwistedCubicParam K p.val) = 0 at hp'
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hp'
  change standardTwistedCubicParam K p.val ∈
    Ideal.span ({standardTwistedCubicParam K F} : Set (MvPolynomial (Fin 2) K)) at hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨q, hq⟩ := hmem
  have hqP : q * standardTwistedCubicParam K F = standardTwistedCubicParam K p.val := by
    rw [mul_comm]
    exact hq.symm
  have hqhom : q.IsHomogeneous (3 * (d - 3)) := by
    apply homogeneous_of_mul_right (standardTwistedCubicParam_homogeneous hF) hnonzero
    rw [show 3 * (d - 3) + 9 = 3 * d by omega, hqP]
    exact standardTwistedCubicParam_homogeneous p.property
  obtain ⟨r, hr⟩ := standardTwistedCubicParamDegreeMap_surjective (K := K) (d - 3)
    ⟨q, hqhom⟩
  have hrval : standardTwistedCubicParam K r.val = q := congrArg Subtype.val hr
  have hzero : standardTwistedCubicParam K (p.val - F * r.val) = 0 := by
    rw [map_sub, map_mul, hrval, ← hqP]
    ring
  have hstd : p.val - F * r.val ∈ standardTwistedCubicIdeal K := by
    rw [standardTwistedCubicIdeal_eq_ker]
    exact hzero
  change p.val ∈ standardTwistedCubicIdeal K ⊔ Ideal.span {F}
  rw [show p.val = (p.val - F * r.val) + F * r.val by ring]
  apply add_mem
  · exact (le_sup_left : standardTwistedCubicIdeal K ≤
      standardTwistedCubicIdeal K ⊔ Ideal.span {F}) hstd
  · apply (le_sup_right : Ideal.span {F} ≤
      standardTwistedCubicIdeal K ⊔ Ideal.span {F})
    rw [mul_comm]
    exact Ideal.mul_mem_left (Ideal.span {F}) r.val
      (Ideal.subset_span (Set.mem_singleton F))

/-- In degrees at least three, the projective and binary quotient components
are identified faithfully by restriction along the twisted cubic. -/
theorem standardTwistedCubicCubicComparisonMap_injective
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : standardTwistedCubicParam K F ≠ 0)
    (d : ℕ) (hd : 3 ≤ d) :
    Function.Injective (standardTwistedCubicCubicComparisonMap F hF d) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro y hy
  obtain ⟨p, hp, hpy⟩ := y.property
  let z : grading (standardTwistedCubicCubicIntersectionIdeal F hF) d :=
    ⟨standardTwistedCubicCubicIntersectionProjection F hF d ⟨p, hp⟩,
      (show Ideal.Quotient.mk (standardTwistedCubicCubicIntersectionIdeal F hF).toIdeal p ∈
        grading (standardTwistedCubicCubicIntersectionIdeal F hF) d by
        exact ⟨p, hp, rfl⟩)⟩
  have hzy : z = y := by
    apply Subtype.ext
    exact hpy
  have hcompz : standardTwistedCubicCubicComparisonMap F hF d z = 0 := by
    rw [hzy]
    exact hy
  have hprojection : standardTwistedCubicCubicProjection F hF d ⟨p, hp⟩ = 0 := by
    exact (standardTwistedCubicCubicComparisonMap_projection F hF d ⟨p, hp⟩).symm.trans hcompz
  have hmem := mem_standardTwistedCubicCubicIntersectionIdeal_of_projection_eq_zero
    F hF hnonzero d hd ⟨p, hp⟩ hprojection
  apply Subtype.ext
  rw [← hpy]
  change Ideal.Quotient.mk (standardTwistedCubicCubicIntersectionIdeal F hF).toIdeal p = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem

/-- The degree-wise comparison is an isomorphism after the cubic has been
imposed and it does not contain the twisted cubic. -/
theorem standardTwistedCubicCubicComparisonMap_bijective
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : standardTwistedCubicParam K F ≠ 0)
    (d : ℕ) (hd : 3 ≤ d) :
    Function.Bijective (standardTwistedCubicCubicComparisonMap F hF d) :=
  ⟨standardTwistedCubicCubicComparisonMap_injective F hF hnonzero d hd,
    standardTwistedCubicCubicComparisonMap_surjective F hF d⟩

/-- The projective twisted-cubic--cubic intersection has constant
degree-`d` homogeneous coordinate dimension nine from degree three onward. -/
theorem standardTwistedCubicCubicIntersection_grade_finrank
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : standardTwistedCubicParam K F ≠ 0)
    (d : ℕ) (hd : 3 ≤ d) :
    Module.finrank K (grading (standardTwistedCubicCubicIntersectionIdeal F hF) d) = 9 := by
  let e := LinearEquiv.ofBijective (standardTwistedCubicCubicComparisonMap F hF d)
    (standardTwistedCubicCubicComparisonMap_bijective F hF hnonzero d hd)
  calc
    Module.finrank K (grading (standardTwistedCubicCubicIntersectionIdeal F hF) d) =
        Module.finrank K (grading (equationIdeal (standardTwistedCubicParam K F)
          (standardTwistedCubicParam_homogeneous hF)) (3 * d)) := e.finrank_eq
    _ = 9 := by
      have hbinary := binary_projective_grade_finrank (standardTwistedCubicParam K F)
        (standardTwistedCubicParam_homogeneous hF) hnonzero (3 * (d - 3))
      have hdegree : 3 * (d - 3) + 9 = 3 * d := by omega
      rw [hdegree] at hbinary
      exact hbinary

/-- A cubic that does not contain the standard twisted cubic cuts it in an
actual finite projective scheme. -/
theorem standardTwistedCubicCubicIntersection_isFinite [Infinite K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : standardTwistedCubicParam K F ≠ 0) :
    IsFinite (toBase (standardTwistedCubicCubicIntersectionIdeal F hF)) := by
  apply projective_finite_of_hilbert_bound
    (standardTwistedCubicCubicIntersectionIdeal F hF) 3 9
  intro d hd
  exact (standardTwistedCubicCubicIntersection_grade_finrank F hF hnonzero d hd).le

/-- The finite intersection of a non-contained cubic with the standard
twisted cubic has scheme rank nine. -/
theorem standardTwistedCubicCubicIntersection_finiteSchemeRank [Infinite K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    (hnonzero : standardTwistedCubicParam K F ≠ 0)
    [IsFinite (toBase (standardTwistedCubicCubicIntersectionIdeal F hF))] :
    AllCharacteristics.finiteSchemeRank
      (toBase (standardTwistedCubicCubicIntersectionIdeal F hF)) = 9 := by
  apply projective_length_of_eventual_hilbert
    (standardTwistedCubicCubicIntersectionIdeal F hF) 3 9
  intro d hd
  exact standardTwistedCubicCubicIntersection_grade_finrank F hF hnonzero d hd

end QuarticNet
end PfaffianDescent
