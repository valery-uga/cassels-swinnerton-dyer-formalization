import PfaffianDescent.VoisinTwelvePointEvaluationFaithful
import PfaffianDescent.VoisinQuadraticPencilHilbertDetection
import PfaffianDescent.VoisinRegularSequenceCriteria
import PfaffianDescent.PolynomialIdealDescent

/-!
# Hilbert bound from twelve reduced projective intersection points

Evaluation at twelve projective points bounds every positive homogeneous
piece of a radical cubic--quadric--quadric quotient. Consequently the second
quadric is regular modulo the cubic and first quadric, provided the latter
are relatively prime.
-/

namespace PfaffianDescent

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

section

variable {K : Type*} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem twelve_point_triple_component_finrank_le_twelve
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hrad : (tripleCompleteIntersectionIdeal p q r).IsRadical)
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K
      (tripleCompleteIntersectionIdeal p q r))
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K
      (tripleCompleteIntersectionIdeal p q r),
      y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x i)
    (d : ℕ) (hd : 0 < d) :
    Module.finrank K (tripleCompleteIntersectionComponent p q r d) ≤ 12 := by
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let Q := homogeneousIdealPieceQuotientMap I d
  let E := homogeneousSectionRestriction (K := K)
    (fun j i => x i j : Fin 4 → Fin 12 → K) d
  have hker : LinearMap.ker E = LinearMap.ker Q := by
    ext s
    simp only [LinearMap.mem_ker]
    constructor
    · intro hs
      have hs0 : ∀ i, MvPolynomial.aeval (x i) s.1 = 0 := by
        intro i
        have hi := congrArg (fun z : Fin 12 → K => z i) hs
        simpa only [E, homogeneousSectionRestriction_apply, Pi.zero_apply,
          twelve_point_product_evaluation_apply] using hi
      have hmem : s.1 ∈ tripleCompleteIntersectionIdeal p q r :=
        homogeneous_mem_ideal_of_twelve_projective_evaluations_zero
          (tripleCompleteIntersectionIdeal p q r) hrad x hcover
          d hd s.1 s.2 hs0
      apply Subtype.ext
      change Ideal.Quotient.mk I.toIdeal s.1 = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hmem
    · intro hs
      have hs' := congrArg Subtype.val hs
      have hmem : s.1 ∈ tripleCompleteIntersectionIdeal p q r := by
        change Ideal.Quotient.mk I.toIdeal s.1 = 0 at hs'
        exact (Ideal.Quotient.eq_zero_iff_mem).mp hs'
      apply funext
      intro i
      have hzero : MvPolynomial.aeval (x i) s.1 = 0 := by
        simpa using hpoints i s.1 hmem
      simpa only [E, homogeneousSectionRestriction_apply, Pi.zero_apply,
        twelve_point_product_evaluation_apply] using hzero
  have hQsurj : Function.Surjective Q :=
    homogeneousIdealPieceQuotientMap_surjective I d
  have hdim := Q.finrank_range_add_finrank_ker
  have hdimE := E.finrank_range_add_finrank_ker
  have hQrange : LinearMap.range Q = ⊤ :=
    LinearMap.range_eq_top.mpr hQsurj
  have hErange : Module.finrank K (LinearMap.range E) ≤ 12 := by
    have hle := LinearMap.finrank_le_finrank_of_injective
      (LinearMap.range E).injective_subtype
    simpa using hle
  change Module.finrank K (grading I d) ≤ 12
  rw [hQrange, finrank_top] at hdim
  rw [← hker] at hdim
  omega

theorem twelve_point_cubic_two_quadric_regular
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q)
    (hrad : (tripleCompleteIntersectionIdeal p q r).IsRadical)
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K
      (tripleCompleteIntersectionIdeal p q r))
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K
      (tripleCompleteIntersectionIdeal p q r),
      y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x i) :
    ∀ f : MvPolynomial (Fin 4) K,
      r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  apply regular_of_eventually_cubic_two_quadrics_finrank_le_twelve
    p q r hp hq hr hp0 hrel
  refine ⟨1, ?_⟩
  intro d hd
  exact twelve_point_triple_component_finrank_le_twelve
    p q r hp hq hr hrad x hpoints hcover d hd

/-- On a smooth cubic the first nonzero quadric is automatically relatively
prime to the cubic, so reduced twelve-point cone coverage alone makes the
second quadric a regular member of the pencil. -/
theorem twelve_point_smooth_cubic_two_quadric_regular
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0)
    [AlgebraicGeometry.Smooth (hypersurfaceToBase p hp)]
    (hrad : (tripleCompleteIntersectionIdeal p q r).IsRadical)
    (x : Fin 12 → Fin 4 → K)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus K
      (tripleCompleteIntersectionIdeal p q r))
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus K
      (tripleCompleteIntersectionIdeal p q r),
      y = 0 ∨ ∃ (i : Fin 12) (c : K), y = c • x i) :
    ∀ f : MvPolynomial (Fin 4) K,
      r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  have hpprime : Prime p := by
    exact (Ideal.span_singleton_prime hp0).mp
      (principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0)
  have hrel : IsRelPrime p q :=
    isRelPrime_of_prime_homogeneous_degree_lt hp hq hpprime hq0 (by decide)
  exact twelve_point_cubic_two_quadric_regular
    p q r hp hq hr hp0 hrel hrad x hpoints hcover

end

/-! The geometric twelve points may appear only after field extension. -/

theorem twelve_point_cubic_two_quadric_regular_descends
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hp0L : p.map (algebraMap K L) ≠ 0)
    (hrelL : IsRelPrime (p.map (algebraMap K L))
      (q.map (algebraMap K L)))
    (hrad : (tripleCompleteIntersectionIdeal
      (p.map (algebraMap K L)) (q.map (algebraMap K L))
      (r.map (algebraMap K L))).IsRadical)
    (x : Fin 12 → Fin 4 → L)
    (hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus L
      (tripleCompleteIntersectionIdeal
        (p.map (algebraMap K L)) (q.map (algebraMap K L))
        (r.map (algebraMap K L))))
    (hcover : ∀ y ∈ MvPolynomial.zeroLocus L
      (tripleCompleteIntersectionIdeal
        (p.map (algebraMap K L)) (q.map (algebraMap K L))
        (r.map (algebraMap K L))),
      y = 0 ∨ ∃ (i : Fin 12) (c : L), y = c • x i) :
    ∀ f : MvPolynomial (Fin 4) K,
      r * f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        f ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
  let φ := algebraMap K L
  have hregularL := twelve_point_cubic_two_quadric_regular
    (p.map φ) (q.map φ) (r.map φ)
    (hp.map φ) (hq.map φ) (hr.map φ)
    hp0L hrelL hrad x hpoints hcover
  intro f hf
  have hfL : (r.map φ) * (f.map φ) ∈
      Ideal.span ({p.map φ, q.map φ} : Set (MvPolynomial (Fin 4) L)) := by
    have hm := Ideal.mem_map_of_mem (MvPolynomial.map φ) hf
    simpa [Ideal.map_span, Set.image_insert_eq, Set.image_singleton] using hm
  have hmemL := hregularL (f.map φ) hfL
  let Q : Fin 2 → MvPolynomial (Fin 4) K := ![p, q]
  have hrange : Set.range Q = ({p, q} : Set (MvPolynomial (Fin 4) K)) := by
    ext s
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [Q]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [Q]⟩
      · exact ⟨1, by simp [Q]⟩
  have hrangeL : Set.range (fun i : Fin 2 => (Q i).map φ) =
      ({p.map φ, q.map φ} : Set (MvPolynomial (Fin 4) L)) := by
    ext s
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [Q]
    · rintro (rfl | rfl)
      · exact ⟨0, by simp [Q]⟩
      · exact ⟨1, by simp [Q]⟩
  have hdesc : f ∈ Ideal.span (Set.range Q) := by
    apply polynomial_mem_span_map_range_descends (k := K) (K := L) Q f
    rwa [hrangeL]
  rwa [hrange] at hdesc

end PfaffianDescent
