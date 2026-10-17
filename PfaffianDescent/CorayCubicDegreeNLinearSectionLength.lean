import PfaffianDescent.TripleCompleteIntersectionHilbert
import PfaffianDescent.ProjectiveFiniteOfHilbertBound
import PfaffianDescent.ProjectiveLengthOfHilbert
import Mathlib.Tactic.Linarith

/-! Actual degree-(3,n,1) complete intersection: finite scheme and length
3*n, derived from the genuine graded Koszul resolution. The third equation
is explicitly a nonzerodivisor modulo (p,q); its geometric selection is NOT
asserted. No desired Hilbert value, finite scheme or degree is input.
SOURCE ONLY / UNVERIFIED; root alone compiles/audits. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry Module MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem six_mul_choose_add_three (a : ℕ) :
    6 * (a + 3).choose 3 = (a + 3) * (a + 2) * (a + 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (a + 3) 3
  rw [show Nat.factorial 3 = 6 by decide] at h
  have htwo : a + 3 - 2 = a + 1 := by omega
  have hone : a + 3 - 1 = a + 2 := by omega
  simpa only [Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.sub_zero, htwo, hone, mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc]
    using h.symm

/-- The actual homogeneous quotient by p,q,H has constant Hilbert
function 3*n from degree n+4. No genus or line-bundle degree premise. -/
theorem cubic_degree_n_linear_section_hilbert_three_mul
    (p q H : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (hH : H.IsHomogeneous 1)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      H * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)))
    (d : ℕ) :
    finrank K (tripleCompleteIntersectionComponent p q H (d + n + 4)) = 3 * n := by
  have hdim := tripleCompleteIntersection_hilbert_identity
    p q H hp hq hH hp0 hq0 hrel hregular d
  have hdim' :
      finrank K (tripleCompleteIntersectionComponent p q H (d + n + 4)) +
        ((d + n + 4).choose 3 + (d + 7).choose 3 + (d + n + 6).choose 3) +
        (d + 3).choose 3 =
      (d + n + 7).choose 3 +
        ((d + 4).choose 3 + (d + n + 3).choose 3 + (d + 6).choose 3) := by
    have hindex : d + 3 + n + 1 = d + n + 4 := by omega
    rw [hindex] at hdim
    simp only [four_homogeneous_finrank] at hdim
    have hA : d + n + 1 + 3 = d + n + 4 := by omega
    have hB : d + 3 + 1 + 3 = d + 7 := by omega
    have hC : d + 3 + n + 3 = d + n + 6 := by omega
    have hD : d + n + 4 + 3 = d + n + 7 := by omega
    have hE : d + 1 + 3 = d + 4 := by omega
    have hF : d + 3 + 3 = d + 6 := by omega
    simpa only [hA, hB, hC, hD, hE, hF] using hdim
  have hscaled := congrArg (fun a : ℕ => 6 * a) hdim'
  simp only [Nat.mul_add] at hscaled
  simp only [Nat.add_assoc] at hscaled ⊢
  have h1 := six_mul_choose_add_three (d + n + 1)
  have h2 := six_mul_choose_add_three (d + 4)
  have h3 := six_mul_choose_add_three (d + n + 3)
  have h4 := six_mul_choose_add_three d
  have h5 := six_mul_choose_add_three (d + n + 4)
  have h6 := six_mul_choose_add_three (d + 1)
  have h7 := six_mul_choose_add_three (d + n)
  have h8 := six_mul_choose_add_three (d + 3)
  simp only [Nat.add_assoc] at h1 h2 h3 h5 h6 h7 h8
  rw [h1, h2, h3, h4, h5, h6, h7, h8] at hscaled
  nlinarith only [hscaled]

/-- The literal projective linear section is finite over the ORIGINAL K,
internally from its derived Hilbert function. -/
theorem cubic_degree_n_linear_section_finite
    (p q H : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (hH : H.IsHomogeneous 1)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      H * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH)) := by
  apply projective_finite_of_hilbert_bound
    (tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH) (n + 4) (3 * n)
  intro m hm
  change finrank K (tripleCompleteIntersectionComponent p q H m) ≤ 3 * n
  have hdim := cubic_degree_n_linear_section_hilbert_three_mul
    p q H hp hq hH hp0 hq0 hrel hregular (m - (n + 4))
  have hindex : m - (n + 4) + n + 4 = m := by omega
  rw [hindex] at hdim
  exact hdim.le

/-- Scheme-theoretic length, including all nonreduced multiplicities and
full ORIGINAL-K residue degrees, is 3*n. -/
theorem cubic_degree_n_linear_section_length_three_mul [Infinite K]
    (p q H : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n) (hH : H.IsHomogeneous 1)
    (hp0 : p ≠ 0) (hq0 : q ≠ 0) (hrel : IsRelPrime p q)
    (hregular : ∀ x : MvPolynomial (Fin 4) K,
      H * x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
        x ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) :
    letI := cubic_degree_n_linear_section_finite p q H hp hq hH hp0 hq0 hrel hregular
    AllCharacteristics.finiteSchemeRank
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH)) = 3 * n := by
  letI := cubic_degree_n_linear_section_finite p q H hp hq hH hp0 hq0 hrel hregular
  apply projective_length_of_eventual_hilbert
    (tripleCompleteIntersectionHomogeneousIdeal p q H hp hq hH) (n + 4) (3 * n)
  intro m hm
  change finrank K (tripleCompleteIntersectionComponent p q H m) = 3 * n
  have hdim := cubic_degree_n_linear_section_hilbert_three_mul
    p q H hp hq hH hp0 hq0 hrel hregular (m - (n + 4))
  have hindex : m - (n + 4) + n + 4 = m := by omega
  rw [hindex] at hdim
  exact hdim

end PfaffianDescent.Coray
