import AllCharacteristics.FlatPrincipalQuotient
import AllCharacteristics.MvPolynomialRegularCoefficient
import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Flat polynomial hypersurfaces on coefficient opens

A polynomial quotient with a unit coefficient is flat over its coefficient
ring. Localizing at any one coefficient makes that coefficient a unit, giving
flatness on each corresponding coefficient open. The coefficient need not be
a leading coefficient and the base may have zero-divisors.
-/

open scoped nonZeroDivisors
namespace AllCharacteristics
universe u v w

/-- A multivariate polynomial with a unit coefficient defines a flat affine
hypersurface over every commutative base ring. -/
theorem mvPolynomial_quotient_flat_of_isUnit_coeff
    {R : Type u} [CommRing R] {σ : Type v} [Finite σ]
    (p : MvPolynomial σ R) (m : σ →₀ ℕ) (hm : IsUnit (p.coeff m)) :
    Module.Flat R (MvPolynomial σ R ⧸ Ideal.span {p}) := by
  apply quotient_flat_of_nonZeroDivisors_mod_base_ideals p
  intro I
  let e := MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) I
  apply mem_nonZeroDivisors_of_injective e.symm.injective
  change (MvPolynomial.eval₂Hom (MvPolynomial.C.comp (Ideal.Quotient.mk I))
    MvPolynomial.X) p ∈ (MvPolynomial σ (R ⧸ I))⁰
  rw [← MvPolynomial.map_eq_eval₂Hom_C_comp]
  apply mvPolynomial_mem_nonZeroDivisors_of_isUnit_coeff _ m
  simpa only [MvPolynomial.coeff_map] using hm.map (Ideal.Quotient.mk I)

/-- After localizing at a coefficient, the mapped polynomial quotient is
flat over the localized coefficient ring. -/
theorem mvPolynomial_quotient_flat_after_localizing_coeff
    {R : Type u} [CommRing R] {σ : Type v} [Finite σ]
    (p : MvPolynomial σ R) (m : σ →₀ ℕ)
    (S : Type w) [CommRing S] [Algebra R S] [IsLocalization.Away (p.coeff m) S] :
    Module.Flat S (MvPolynomial σ S ⧸ Ideal.span {p.map (algebraMap R S)}) := by
  apply mvPolynomial_quotient_flat_of_isUnit_coeff _ m
  rw [MvPolynomial.coeff_map]
  exact IsLocalization.map_units S ⟨p.coeff m, Submonoid.mem_powers _⟩

end AllCharacteristics
