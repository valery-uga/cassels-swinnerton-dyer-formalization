import PfaffianDescent.CoraySmoothCurveHilbert
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The large-degree Hilbert polynomial of the actual selected intersection

The actual graded Koszul resolution gives a binomial-coefficient identity.
Here we derive its linear Hilbert polynomial, with degree coefficient `3*n`
and doubled constant term `-3*n*(n-1)`, for the actual polynomial quotient.
No identification of that constant term with the genus of a projective curve
or its normalization is asserted or supplied as a premise.

STATUS: source draft, UNVERIFIED. Root owns all compiler checks.
-/

namespace PfaffianDescent.Coray

open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

private theorem six_mul_choose_add_three (a : ℕ) :
    6 * (a + 3).choose 3 = (a + 3) * (a + 2) * (a + 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (a + 3) 3
  rw [show Nat.factorial 3 = 6 by decide] at h
  have htwo : a + 3 - 2 = a + 1 := by omega
  have hone : a + 3 - 1 = a + 2 := by omega
  simpa only [Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.sub_zero, htwo, hone, mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc]
    using h.symm

/-- Linear Hilbert polynomial, written without natural-number subtraction.
The degree is any `d+n+3`, hence covers all degrees at least `n+3`. -/
theorem curve_hilbert_polynomial_identity {K : Type u} [Field K] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q) (d : ℕ) :
    2 * finrank K (curveComponent p q (d + n + 3)) + 3 * n * n =
      6 * n * (d + n + 3) + 3 * n := by
  have h := curve_hilbert_choose_identity p q hp hq hp0 hrel d
  have hscaled := congrArg (fun a : ℕ => 6 * a) h
  have hmiddle : 6 * (d + 6).choose 3 = (d + 6) * (d + 5) * (d + 4) := by
    simpa only [Nat.add_assoc] using six_mul_choose_add_three (d + 3)
  have htop : 6 * (d + n + 6).choose 3 =
      (d + n + 6) * (d + n + 5) * (d + n + 4) := by
    simpa only [Nat.add_assoc] using six_mul_choose_add_three (d + n + 3)
  simp only [Nat.mul_add] at hscaled
  rw [six_mul_choose_add_three (d + n), hmiddle, htop,
    six_mul_choose_add_three d] at hscaled
  nlinarith only [hscaled]

/-- The same actual Hilbert function expressed with the usual doubled
constant term. The constant term has not been declared a geometric genus. -/
theorem curve_hilbert_polynomial_identity_of_positive_degree
    {K : Type u} [Field K] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous n)
    (hp0 : p ≠ 0) (hrel : IsRelPrime p q) (hn : 1 ≤ n) (d : ℕ) :
    2 * finrank K (curveComponent p q (d + n + 3)) + 3 * n * (n - 1) =
      6 * n * (d + n + 3) := by
  have h := curve_hilbert_polynomial_identity p q hp hq hp0 hrel d
  have hprod : 3 * n * n = 3 * n * (n - 1) + 3 * n := by
    calc
      3 * n * n = 3 * n * ((n - 1) + 1) :=
        congrArg (fun a : ℕ => 3 * n * a) (Nat.sub_add_cancel hn).symm
      _ = 3 * n * (n - 1) + 3 * n := by ring
  rw [hprod] at h
  omega

/-- Smoothness and actual finite-algebra coordinates select the equation
internally. Its actual quotient has the derived polynomial in large degrees. -/
theorem exists_homogeneous_curve_with_hilbert_polynomial
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (x : Fin 4 → A)
    (hsize : finrank K A < (n + 3).choose 3 - n.choose 3) :
    ∃ q : MvPolynomial (Fin 4) K,
      q.IsHomogeneous n ∧ q.eval₂ (algebraMap K A) x = 0 ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
      (∀ d : ℕ,
        2 * finrank K (curveComponent p q (d + n + 3)) + 3 * n * n =
          6 * n * (d + n + 3) + 3 * n) := by
  obtain ⟨q, hq, hzero, hnot⟩ := exists_homogeneous_curve_equation p hp hp0 n x hsize
  have hrel := isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot
  exact ⟨q, hq, hzero, hnot,
    fun d => curve_hilbert_polynomial_identity p q hp hq hp0 hrel d⟩

end PfaffianDescent.Coray
