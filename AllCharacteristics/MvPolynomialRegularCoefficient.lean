import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Fintype.Option

/-!
# A regular coefficient makes a multivariate polynomial regular

McCoy's univariate theorem extends to finitely many variables by induction:
view a polynomial as univariate over the polynomial ring in the remaining
variables, retaining the chosen coefficient. A unit coefficient therefore
makes the polynomial a non-zero-divisor over every commutative base ring.
-/

open MvPolynomial
open scoped nonZeroDivisors
namespace AllCharacteristics
universe u v

/-- A polynomial in finitely many variables with one non-zero-divisor
coefficient is itself a non-zero-divisor. -/
theorem mvPolynomial_mem_nonZeroDivisors_of_coeff
    {R : Type u} [CommRing R] {σ : Type v} [Finite σ]
    (p : MvPolynomial σ R) (m : σ →₀ ℕ) (hm : p.coeff m ∈ R⁰) :
    p ∈ (MvPolynomial σ R)⁰ := by
  classical
  revert p m
  refine Finite.induction_empty_option
    (P := fun τ ↦ ∀ (q : MvPolynomial τ R) (n : τ →₀ ℕ),
      q.coeff n ∈ R⁰ → q ∈ (MvPolynomial τ R)⁰) ?_ ?_ ?_ σ
  · intro α β e ih q n hn
    let E := renameEquiv R e.symm
    apply mem_nonZeroDivisors_of_injective E.injective
    apply ih (E q) (Finsupp.mapDomain e.symm n)
    change (rename e.symm q).coeff (Finsupp.mapDomain e.symm n) ∈ R⁰
    rwa [coeff_rename_mapDomain e.symm e.symm.injective]
  · intro q n hn
    apply mem_nonZeroDivisors_of_injective (isEmptyRingEquiv R PEmpty).injective
    rw [isEmptyRingEquiv_eq_coeff_zero]
    have hn0 : n = 0 := Subsingleton.elim _ _
    simpa only [hn0] using hn
  · intro α _ ih q n hn
    apply mem_nonZeroDivisors_of_injective (optionEquivLeft R α).injective
    apply Polynomial.mem_nonzeroDivisors_of_coeff_mem (n none)
    apply ih _ n.some
    rwa [optionEquivLeft_coeff_some_coeff_none]

/-- A unit coefficient ensures regularity, without requiring a domain or a
restriction on the characteristic. -/
theorem mvPolynomial_mem_nonZeroDivisors_of_isUnit_coeff
    {R : Type u} [CommRing R] {σ : Type v} [Finite σ]
    (p : MvPolynomial σ R) (m : σ →₀ ℕ) (hm : IsUnit (p.coeff m)) :
    p ∈ (MvPolynomial σ R)⁰ :=
  mvPolynomial_mem_nonZeroDivisors_of_coeff p m hm.mem_nonZeroDivisors

end AllCharacteristics
