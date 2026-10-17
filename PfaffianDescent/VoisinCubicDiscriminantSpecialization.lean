import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Separable

/-!
# Cubic discriminants under coefficient specialization

The cubic discriminant is a polynomial in the four coefficients. When both
the original and specialized polynomials retain degree three, the explicit
formula makes specialization transparent. A single specialized nonzero
discriminant therefore certifies nonvanishing before specialization.
-/

namespace PfaffianDescent

open Polynomial

theorem cubic_discr_map_of_degree_three
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X])
    (hf : f.degree = 3) (hmap : (f.map φ).degree = 3) :
    (f.map φ).discr = φ f.discr := by
  rw [discr_of_degree_eq_three hmap, discr_of_degree_eq_three hf]
  simp only [coeff_map, map_add, map_sub, map_mul, map_pow, map_ofNat]

theorem cubic_discr_ne_zero_of_specialization
    {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (f : R[X])
    (hf : f.degree = 3) (hmap : (f.map φ).degree = 3)
    (hdisc : (f.map φ).discr ≠ 0) : f.discr ≠ 0 := by
  intro h
  rw [cubic_discr_map_of_degree_three φ f hf hmap, h, map_zero] at hdisc
  exact hdisc rfl

/-- In characteristic zero, a nonzero discriminant of a positive-degree
polynomial forces separability. This is the final field-level implication
needed after a generic coefficient discriminant is shown nonzero. -/
theorem polynomial_separable_of_discr_ne_zero
    {K : Type*} [Field K] [CharZero K]
    (f : K[X]) (hpos : 0 < f.degree) (hdisc : f.discr ≠ 0) :
    f.Separable := by
  have hf : f ≠ 0 := by
    intro h
    simp [h] at hpos
  have hres : f.resultant f.derivative ≠ 0 := by
    change resultant f f.derivative f.natDegree f.derivative.natDegree ≠ 0
    rw [natDegree_derivative, resultant_deriv hpos]
    exact mul_ne_zero (mul_ne_zero (by simp) (leadingCoeff_ne_zero.mpr hf)) hdisc
  have hcoprime : IsCoprime f f.derivative := by
    by_contra h
    exact hres ((resultant_eq_zero_iff).mpr ⟨Or.inl hf, h⟩)
  exact (separable_def' f).2 hcoprime

/-- For a cubic over a characteristic-zero field, separability also forces
the discriminant to be nonzero. -/
theorem cubic_discr_ne_zero_of_separable
    {K : Type*} [Field K] [CharZero K]
    (f : K[X]) (hf : f.degree = 3) (hsep : f.Separable) :
    f.discr ≠ 0 := by
  have hpos : 0 < f.degree := by rw [hf]; decide
  have hf0 : f ≠ 0 := by
    intro h
    simp [h] at hf
  have hcoprime : IsCoprime f f.derivative := (separable_def f).mp hsep
  have hres : f.resultant f.derivative ≠ 0 := by
    intro hzero
    exact ((resultant_eq_zero_iff).mp hzero).2 hcoprime
  change resultant f f.derivative f.natDegree f.derivative.natDegree ≠ 0 at hres
  rw [natDegree_derivative, resultant_deriv hpos] at hres
  intro hdisc
  apply hres
  rw [hdisc, mul_zero]

end PfaffianDescent
