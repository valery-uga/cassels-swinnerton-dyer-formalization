import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic.LinearCombination

/-!
The algebraic rigidity calculation for lines on a smooth cubic surface.
If the normal derivatives of a contained line are relatively prime binary
quadratics, a first-order deformation would give a syzygy with linear
coefficients. Such a syzygy is zero. The univariate version also derives
coprimeness from absence of a common root over an algebraically closed field.

This file does not assert finiteness of contained lines or the generic
tangent-section theorem.
-/

namespace AllCharacteristics

open MvPolynomial

/-- A nonzero quadratic cannot divide a polynomial of total degree at most
one. This is the degree obstruction in the normal-bundle calculation. -/
theorem cubicLine_quadratic_not_dvd_linear
    {K σ : Type*} [Field K]
    (q a : MvPolynomial σ K) (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0)
    (ha : a.totalDegree ≤ 1) (ha0 : a ≠ 0) : ¬ q ∣ a := by
  intro hdiv
  have hdeg := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdiv ha0
  rw [hq.totalDegree hq0] at hdeg
  omega

/-- Relatively prime quadratic normal derivatives have no nonzero linear
syzygy. This is the explicit algebra behind `H⁰(N_{L/X}) = 0`. -/
theorem cubicLine_homogeneous_linear_syzygy_eq_zero
    {K σ : Type*} [Field K]
    (q r a b : MvPolynomial σ K)
    (hq : q.IsHomogeneous 2) (hq0 : q ≠ 0)
    (hqr : IsRelPrime q r)
    (ha : a.totalDegree ≤ 1) (hb : b.totalDegree ≤ 1)
    (h : a * q + b * r = 0) : a = 0 ∧ b = 0 := by
  have hdiv : q ∣ b * r := by
    refine ⟨-a, ?_⟩
    linear_combination h
  have hdivb : q ∣ b := hqr.dvd_of_dvd_mul_right hdiv
  have hb0 : b = 0 := by
    by_contra hb0
    exact cubicLine_quadratic_not_dvd_linear q b hq hq0 hb hb0 hdivb
  have haq : a * q = 0 := by simpa only [hb0, zero_mul, add_zero] using h
  exact ⟨(mul_eq_zero.mp haq).resolve_right hq0, hb0⟩

/-- In a coordinate in which the first normal quadratic has degree exactly
two, coprime normal derivatives have no nonzero linear syzygy. -/
theorem cubicLine_polynomial_linear_syzygy_eq_zero
    {K : Type*} [Field K]
    (q r a b : Polynomial K)
    (hq : q.natDegree = 2) (hqr : IsCoprime q r)
    (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1)
    (h : a * q + b * r = 0) : a = 0 ∧ b = 0 := by
  have hq0 : q ≠ 0 := by
    intro hzero
    simp only [hzero, Polynomial.natDegree_zero] at hq
    omega
  have hdiv : q ∣ b * r := by
    refine ⟨-a, ?_⟩
    linear_combination h
  have hdivb : q ∣ b := hqr.dvd_of_dvd_mul_right hdiv
  have hb0 : b = 0 := by
    by_contra hb0
    have hdeg := Polynomial.natDegree_le_of_dvd hdivb hb0
    rw [hq] at hdeg
    omega
  have haq : a * q = 0 := by simpa only [hb0, zero_mul, add_zero] using h
  exact ⟨(mul_eq_zero.mp haq).resolve_right hq0, hb0⟩

/-- The root-free version required by smoothness: simultaneous vanishing of
the two normal derivatives is excluded along the whole affine line. -/
theorem cubicLine_polynomial_linear_syzygy_eq_zero_of_no_common_root
    {K : Type*} [Field K] [IsAlgClosed K]
    (q r a b : Polynomial K)
    (hq : q.natDegree = 2)
    (hno : ∀ x : K, Polynomial.aeval x q ≠ 0 ∨ Polynomial.aeval x r ≠ 0)
    (ha : a.natDegree ≤ 1) (hb : b.natDegree ≤ 1)
    (h : a * q + b * r = 0) : a = 0 ∧ b = 0 := by
  have hqr : IsCoprime q r :=
    (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K q r).2 hno
  exact cubicLine_polynomial_linear_syzygy_eq_zero q r a b hq hqr ha hb h

end AllCharacteristics
