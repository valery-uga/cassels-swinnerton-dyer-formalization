import PfaffianDescent.VoisinGenericFourLineSeparability
import PfaffianDescent.VoisinSplitTwelvePointNumerics
import PfaffianDescent.VoisinTwelvePointEvaluationFaithful

/-!
# Étaleness of the generic split intersection from its length

The universal cubic has a finite split intersection with the two standard
quadrics, and twelve distinct geometric zeros. This file proves its length
is twelve and derives étaleness from those roots.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

/-- The finite generic split intersection has the expected length twelve. -/
theorem generic_split_intersection_rank_twelve
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    letI := generic_split_intersection_finite K φ
    finiteSchemeRank (toBase (tripleCompleteIntersectionHomogeneousIdeal
      ((genericCubicTensor K).map φ).toMvPolynomial
      (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3))
      (cubic_toMvPolynomial_isHomogeneous_three _)
      ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
      ((isHomogeneous_X L 3).mul
        (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
          (isHomogeneous_X L 3))))) = 12 := by
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let q : MvPolynomial (Fin 4) L := X 1 * X 2
  let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
  let hp := cubic_toMvPolynomial_isHomogeneous_three ((genericCubicTensor K).map φ)
  let hq : q.IsHomogeneous 2 := (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
  let hr : r.IsHomogeneous 2 := (isHomogeneous_X L 3).mul
    (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
      (isHomogeneous_X L 3))
  let I := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  letI : IsFinite (toBase I) := generic_split_intersection_finite K φ
  obtain ⟨x, hinj, hzero, hform, -⟩ :=
    exists_generic_four_line_root_triples K φ
  have hform' : ∀ i j k, ∃ t : L,
      x i j k = t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j := by
    intro i j k
    obtain ⟨t, ht⟩ := hform i j k
    refine ⟨t, ?_⟩
    rwa [genericFourLineBase_baseChange_eq K φ,
      genericFourLineDirection_baseChange_eq K φ i j] at ht
  have hroots : ∀ i j k,
      p.eval (x i j k) = 0 ∧ q.eval (x i j k) = 0 ∧
        r.eval (x i j k) = 0 := by
    intro i j k
    obtain ⟨t, ht⟩ := hform' i j k
    have hs := standard_split_quadrics_zero_on_line i j t
    have hpzero := hzero i j k
    rw [ht] at hpzero
    have hev := Cubic.eval_toMvPolynomial (RingHom.id L)
      ((genericCubicTensor K).map φ)
      (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j)
    change p.eval (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) =
      ((genericCubicTensor K).map φ).eval
        (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) at hev
    rw [ht]
    exact ⟨hev.trans hpzero, hs.1, hs.2⟩
  have hX : Nonempty (scheme I) := by
    obtain ⟨t, ht⟩ := hform' 0 0 0
    have hne : x 0 0 0 ≠ 0 := by
      rw [ht]
      exact standardFourLines_genuine 0 0 t
    have hI := tripleCompleteIntersection_vector_zero_of_generators
      p q r hp hq hr (x 0 0 0)
      (hroots 0 0 0).1 (hroots 0 0 0).2.1
      (hroots 0 0 0).2.2
    obtain ⟨z, -⟩ := point_of_coordinates I (RingHom.id L)
      (x 0 0 0) hne hI
    exact ⟨z (IsLocalRing.closedPoint L)⟩
  have hrel : IsRelPrime p q :=
    tripleCompleteIntersection_isRelPrime_of_finite_of_nonempty
      p q r hp hq hr (by decide) hX
  have hpoint : p.eval (Pi.single 0 1 : Fin 4 → L) ≠ 0 :=
    genericCubicTensor_baseChange_standard_point_ne_zero K φ
  have hp0 : p ≠ 0 := by
    intro h
    simp [h] at hpoint
  have hq0 : q ≠ 0 := by simp [q]
  have hregular : ∀ F : MvPolynomial (Fin 4) L,
      r * F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) L)) →
        F ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) L)) :=
    standardFourLines_regular p hp hpoint
  exact cubic_two_quadrics_intersection_length_twelve
    p q r hp hq hr hp0 hq0 hrel hregular

theorem generic_split_intersection_etale_of_rank_twelve
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L)
    (hrank : letI := generic_split_intersection_finite K φ
      finiteSchemeRank (toBase (tripleCompleteIntersectionHomogeneousIdeal
        ((genericCubicTensor K).map φ).toMvPolynomial
        (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3))
        (cubic_toMvPolynomial_isHomogeneous_three _)
        ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
        ((isHomogeneous_X L 3).mul
          (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
            (isHomogeneous_X L 3))))) = 12) :
    letI := generic_split_intersection_finite K φ
    Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      ((genericCubicTensor K).map φ).toMvPolynomial
      (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3))
      (cubic_toMvPolynomial_isHomogeneous_three _)
      ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
      ((isHomogeneous_X L 3).mul
        (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
          (isHomogeneous_X L 3))))) := by
  letI := generic_split_intersection_finite K φ
  obtain ⟨x, hinj, hzero, hform, -⟩ :=
    exists_generic_four_line_root_triples K φ
  have hform' : ∀ i j k, ∃ t : L,
      x i j k = t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j := by
    intro i j k
    obtain ⟨t, ht⟩ := hform i j k
    refine ⟨t, ?_⟩
    rwa [genericFourLineBase_baseChange_eq K φ,
      genericFourLineDirection_baseChange_eq K φ i j] at ht
  apply cubic_two_quadric_etale_of_sheared_four_line_root_equations
    ((genericCubicTensor K).map φ).toMvPolynomial
    (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3))
    (cubic_toMvPolynomial_isHomogeneous_three _)
    ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
    ((isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3))) hrank
    (Pi.single 0 1 : Fin 4 → L) (by simp) x hinj hform'
  intro i j k
  obtain ⟨t, ht⟩ := hform' i j k
  have hs := standard_split_quadrics_zero_on_line i j t
  have hp := hzero i j k
  rw [ht] at hp
  have hev := Cubic.eval_toMvPolynomial (RingHom.id L)
    ((genericCubicTensor K).map φ)
    (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j)
  change ((genericCubicTensor K).map φ).toMvPolynomial.eval
    (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) =
      ((genericCubicTensor K).map φ).eval
        (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) at hev
  rw [ht]
  exact ⟨hev.trans hp, hs.1, hs.2⟩

/-- The generic cubic and the two standard split quadrics form a finite
étale twelve-point complete intersection over the algebraic closure. -/
theorem generic_split_intersection_etale
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    letI := generic_split_intersection_finite K φ
    Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      ((genericCubicTensor K).map φ).toMvPolynomial
      (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3))
      (cubic_toMvPolynomial_isHomogeneous_three _)
      ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
      ((isHomogeneous_X L 3).mul
        (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
          (isHomogeneous_X L 3))))) := by
  exact generic_split_intersection_etale_of_rank_twelve K φ
    (generic_split_intersection_rank_twelve K φ)

theorem standard_split_quadric_pair_linearIndependent
    {L : Type u} [Field L] :
    LinearIndependent L ![
      (X 1 * X 2 : MvPolynomial (Fin 4) L),
      X 3 * (X 1 + X 2 + X 3)] := by
  let q : MvPolynomial (Fin 4) L := X 1 * X 2
  let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
  let v : Fin 4 → L := Pi.single 1 1 + Pi.single 2 1
  let w : Fin 4 → L := Pi.single 3 1
  have hqv : q.eval v = 1 := by
    simp [q, v, Pi.single]
  have hrv : r.eval v = 0 := by
    simp [r, v, Pi.single]
  have hqw : q.eval w = 0 := by
    simp [q, w, Pi.single]
  have hrw : r.eval w = 1 := by
    simp [r, w, Pi.single]
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have hcv := congrArg (MvPolynomial.eval v) hc
  have hcw := congrArg (MvPolynomial.eval w) hc
  have hc0 : c 0 = 0 := by
    simpa [q, r, hqv, hrv, Fin.sum_univ_succ] using hcv
  have hc1 : c 1 = 0 := by
    simpa [q, r, hqw, hrw, Fin.sum_univ_succ] using hcw
  intro i
  fin_cases i <;> assumption

/-- The degree-two coordinate quotient of the generic split twelve-point
intersection has dimension eight. -/
theorem generic_split_intersection_quadratic_quotient_rank_eight
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    Module.finrank L (grading
      (tripleCompleteIntersectionHomogeneousIdeal
        ((genericCubicTensor K).map φ).toMvPolynomial
        (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3))
        (cubic_toMvPolynomial_isHomogeneous_three _)
        ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
        ((isHomogeneous_X L 3).mul
          (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
            (isHomogeneous_X L 3)))) 2) = 8 := by
  exact cubic_two_quadric_quadratic_quotient_finrank_eq_eight
    ((genericCubicTensor K).map φ).toMvPolynomial
    (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3))
    (cubic_toMvPolynomial_isHomogeneous_three _)
    ((isHomogeneous_X L 1).mul (isHomogeneous_X L 2))
    ((isHomogeneous_X L 3).mul
      (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
        (isHomogeneous_X L 3)))
    standard_split_quadric_pair_linearIndependent

/-- Every vector annihilated by the two standard split quadrics lies on
one of their four explicit lines through the first coordinate point. -/
theorem standard_split_quadrics_four_line_span
    {L : Type u} [Field L] (y : Fin 4 → L)
    (hq : (X 1 * X 2 : MvPolynomial (Fin 4) L).eval y = 0)
    (hr : (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval y = 0) :
    ∃ (i j : Fin 2) (s t : L),
      y = s • (Pi.single 0 1 : Fin 4 → L) + t • lineDirection i j := by
  have hq' : y 1 * y 2 = 0 := by
    simpa [MvPolynomial.eval_mul] using hq
  have hr' : y 3 * (y 1 + y 2 + y 3) = 0 := by
    simpa [MvPolynomial.eval_mul, MvPolynomial.eval_add] using hr
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, (if i = 0 then y 1 else y 2) = 0 := by
    rcases mul_eq_zero.mp hq' with h1 | h2
    · exact ⟨0, by simpa using h1⟩
    · exact ⟨1, by simpa using h2⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin 2,
      (if j = 0 then y 3 else y 1 + y 2 + y 3) = 0 := by
    rcases mul_eq_zero.mp hr' with h3 | hsum
    · exact ⟨0, by simpa using h3⟩
    · exact ⟨1, by simpa using hsum⟩
  refine ⟨i, j, y 0, if i = 0 then y 2 else y 1, ?_⟩
  fin_cases i <;> fin_cases j <;>
    simp at hi hj ⊢
  all_goals
    funext m
    fin_cases m <;>
      simp [lineDirection, Pi.single] at hi hj ⊢ <;> grind

/-- The four triples of generic roots cover the entire affine cone of the
split cubic--quadric--quadric intersection, up to scalar multiples. -/
theorem exists_generic_split_roots_cover_affine_cone
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    ∃ x : Fin 2 → Fin 2 → Fin 3 → Fin 4 → L,
      (∀ i j k,
        ((genericCubicTensor K).map φ).toMvPolynomial.eval (x i j k) = 0 ∧
        (X 1 * X 2 : MvPolynomial (Fin 4) L).eval (x i j k) = 0 ∧
        (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval
          (x i j k) = 0) ∧
      (∀ y : Fin 4 → L,
        ((genericCubicTensor K).map φ).toMvPolynomial.eval y = 0 →
        (X 1 * X 2 : MvPolynomial (Fin 4) L).eval y = 0 →
        (X 3 * (X 1 + X 2 + X 3) : MvPolynomial (Fin 4) L).eval y = 0 →
        y = 0 ∨ ∃ (i j : Fin 2) (k : Fin 3) (c : L),
          y = c • x i j k) := by
  obtain ⟨x, -, hzero, hform, hcover⟩ :=
    exists_generic_four_line_root_triples K φ
  have hform' : ∀ i j k, ∃ t : L,
      x i j k = t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j := by
    intro i j k
    obtain ⟨t, ht⟩ := hform i j k
    refine ⟨t, ?_⟩
    rwa [genericFourLineBase_baseChange_eq K φ,
      genericFourLineDirection_baseChange_eq K φ i j] at ht
  refine ⟨x, ?_, ?_⟩
  · intro i j k
    obtain ⟨t, ht⟩ := hform' i j k
    have hs := standard_split_quadrics_zero_on_line i j t
    have hp := hzero i j k
    rw [ht] at hp
    have hev := Cubic.eval_toMvPolynomial (RingHom.id L)
      ((genericCubicTensor K).map φ)
      (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j)
    change ((genericCubicTensor K).map φ).toMvPolynomial.eval
      (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) =
        ((genericCubicTensor K).map φ).eval
          (t • (Pi.single 0 1 : Fin 4 → L) + lineDirection i j) at hev
    rw [ht]
    exact ⟨hev.trans hp, hs.1, hs.2⟩
  intro y hp hq hr
  obtain ⟨i, j, s, t, hspan⟩ :=
    standard_split_quadrics_four_line_span y hq hr
  have hc := hcover i j s t
  rw [genericFourLineBase_baseChange_eq K φ,
    genericFourLineDirection_baseChange_eq K φ i j] at hc
  have hev := Cubic.eval_toMvPolynomial (RingHom.id L)
    ((genericCubicTensor K).map φ)
    (s • (Pi.single 0 1 : Fin 4 → L) + t • lineDirection i j)
  change ((genericCubicTensor K).map φ).toMvPolynomial.eval
    (s • (Pi.single 0 1 : Fin 4 → L) + t • lineDirection i j) =
      ((genericCubicTensor K).map φ).eval
        (s • (Pi.single 0 1 : Fin 4 → L) + t • lineDirection i j) at hev
  rw [hspan] at hp
  rcases hc (hev.symm ▸ hp) with hz | ⟨k, c, heq⟩
  · exact Or.inl (hspan.trans hz)
  · exact Or.inr ⟨i, j, k, c, hspan.trans heq⟩

/-- Assuming radicality of the homogeneous ideal, eight of the twelve
generic split roots give a surjective quadratic evaluation map. -/
theorem generic_split_exists_eight_surjective_quadratic_evaluations_of_radical
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L)
    (hrad : (tripleCompleteIntersectionIdeal
      ((genericCubicTensor K).map φ).toMvPolynomial
      (X 1 * X 2) (X 3 * (X 1 + X 2 + X 3))).IsRadical) :
    ∃ (x : Fin 12 → Fin 4 → L) (κ : Type) (a : κ → Fin 12)
      (inst : Fintype κ),
      Function.Injective a ∧ @Fintype.card κ inst = 8 ∧
      Function.Surjective
        (homogeneousSectionRestriction (K := L)
          (fun (j : Fin 4) (t : κ) => x (a t) j) 2) := by
  classical
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let q : MvPolynomial (Fin 4) L := X 1 * X 2
  let r : MvPolynomial (Fin 4) L := X 3 * (X 1 + X 2 + X 3)
  let hp := cubic_toMvPolynomial_isHomogeneous_three ((genericCubicTensor K).map φ)
  let hq : q.IsHomogeneous 2 := (isHomogeneous_X L 1).mul (isHomogeneous_X L 2)
  let hr : r.IsHomogeneous 2 := (isHomogeneous_X L 3).mul
    (((isHomogeneous_X L 1).add (isHomogeneous_X L 2)).add
      (isHomogeneous_X L 3))
  let I := tripleCompleteIntersectionIdeal p q r
  obtain ⟨z, hroots, hcover⟩ := exists_generic_split_roots_cover_affine_cone K φ
  let e : Fin 12 ≃ Fin 2 × Fin 2 × Fin 3 :=
    (Fintype.equivFinOfCardEq (by decide :
      Fintype.card (Fin 2 × Fin 2 × Fin 3) = 12)).symm
  let x : Fin 12 → Fin 4 → L := fun i => z (e i).1 (e i).2.1 (e i).2.2
  have hpoints : ∀ i, x i ∈ MvPolynomial.zeroLocus L I := by
    intro i
    have hv := hroots (e i).1 (e i).2.1 (e i).2.2
    intro f hf
    have hgen := tripleCompleteIntersection_vector_zero_of_generators
      p q r hp hq hr (x i) hv.1 hv.2.1 hv.2.2
    exact hgen f (by simpa [I, tripleCompleteIntersectionHomogeneousIdeal_toIdeal] using hf)
  have hcover' : ∀ y ∈ MvPolynomial.zeroLocus L I,
      y = 0 ∨ ∃ (i : Fin 12) (c : L), y = c • x i := by
    intro y hy
    have hpzero : p.eval y = 0 := hy p (by
      change p ∈ Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) L))
      exact Ideal.subset_span (by simp))
    have hqzero : q.eval y = 0 := hy q (by
      change q ∈ Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) L))
      exact Ideal.subset_span (by simp))
    have hrzero : r.eval y = 0 := hy r (by
      change r ∈ Ideal.span ({p, q, r} : Set (MvPolynomial (Fin 4) L))
      exact Ideal.subset_span (by simp))
    rcases hcover y hpzero hqzero hrzero with hz | ⟨i, j, k, c, hc⟩
    · exact Or.inl hz
    · exact Or.inr ⟨e.symm (i, j, k), c, by simpa [x] using hc⟩
  have hqr : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2),
        ⟨r, hr⟩] :=
    homogeneous_quadric_pair_linearIndependent_of_polynomials
      q r hq hr standard_split_quadric_pair_linearIndependent
  obtain ⟨κ, a, inst, ha, hcard, hsurj, -⟩ :=
    twelve_point_exists_eight_split_restriction_surjective
      p q r hp hq hr hqr I rfl hrad x hpoints hcover'
  exact ⟨x, κ, a, inst, ha, hcard, hsurj⟩

/-- The direct quadratic-detection route starts with this interpolation
fact: a polynomial of degree at most two cannot vanish at three distinct
line parameters unless it is zero. -/
theorem quadratic_line_polynomial_zero_of_three_distinct_roots
    {L : Type u} [Field L]
    (f : Polynomial L) (hdegree : f.natDegree ≤ 2)
    (t : Fin 3 → L) (hinj : Function.Injective t)
    (hroot : ∀ i, f.eval (t i) = 0) : f = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero f hinj hroot
  simpa using Nat.lt_succ_of_le hdegree

end PfaffianDescent
