import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Leading terms under injective coefficient maps

Injective changes of the coefficient ring preserve polynomial support and
therefore preserve the leading data used by division and S-polynomials.
-/

namespace PfaffianDescent

open MvPolynomial

universe u v

/-- Injective coefficient maps preserve the leading exponent. -/
theorem monomialOrder_degree_map_of_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (m : MonomialOrder (Fin 4)) (p : MvPolynomial (Fin 4) R) :
    m.degree (MvPolynomial.map φ p) = m.degree p := by
  simp only [MonomialOrder.degree, MvPolynomial.support_map_of_injective p hφ]

/-- Injective coefficient maps preserve the leading coefficient by mapping it. -/
theorem monomialOrder_leadingCoeff_map_of_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (m : MonomialOrder (Fin 4)) (p : MvPolynomial (Fin 4) R) :
    m.leadingCoeff (MvPolynomial.map φ p) = φ (m.leadingCoeff p) := by
  simp only [MonomialOrder.leadingCoeff,
    monomialOrder_degree_map_of_injective φ hφ m p, MvPolynomial.coeff_map]

/-- Unit leading coefficients remain units after an injective coefficient change. -/
theorem monomialOrder_isUnit_leadingCoeff_map_of_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (m : MonomialOrder (Fin 4)) (p : MvPolynomial (Fin 4) R)
    (hp : IsUnit (m.leadingCoeff p)) :
    IsUnit (m.leadingCoeff (MvPolynomial.map φ p)) := by
  rw [monomialOrder_leadingCoeff_map_of_injective φ hφ m p]
  exact hp.map φ

/-- A leading coefficient becomes a unit after an injective coefficient
change that makes one of its multiples a unit. -/
theorem monomialOrder_isUnit_leadingCoeff_map_of_dvd_unit
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (m : MonomialOrder (Fin 4)) (p : MvPolynomial (Fin 4) R)
    (e : R) (hdiv : m.leadingCoeff p ∣ e) (he : IsUnit (φ e)) :
    IsUnit (m.leadingCoeff (MvPolynomial.map φ p)) := by
  rw [monomialOrder_leadingCoeff_map_of_injective φ hφ m p]
  exact isUnit_of_dvd_unit (map_dvd φ hdiv) he

/-- S-polynomials commute with injective coefficient maps. -/
theorem monomialOrder_sPolynomial_map_of_injective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Injective φ)
    (m : MonomialOrder (Fin 4))
    (p q : MvPolynomial (Fin 4) R) :
    MvPolynomial.map φ (m.sPolynomial p q) =
      m.sPolynomial (MvPolynomial.map φ p) (MvPolynomial.map φ q) := by
  rw [m.sPolynomial_def, m.sPolynomial_def]
  simp only [map_sub, map_mul, MvPolynomial.map_monomial,
    monomialOrder_degree_map_of_injective φ hφ,
    monomialOrder_leadingCoeff_map_of_injective φ hφ]

/-- Multiplying both inputs by the same scalar multiplies their
S-polynomial by the square of that scalar. -/
theorem monomialOrder_sPolynomial_C_mul_same_scalar
    {F : Type u} [Field F] (m : MonomialOrder (Fin 4))
    (c : F) (f g : MvPolynomial (Fin 4) F) :
    m.sPolynomial (MvPolynomial.C c * f) (MvPolynomial.C c * g) =
      MvPolynomial.C (c * c) * m.sPolynomial f g := by
  simpa only [zero_add, tsub_self, MvPolynomial.monomial_zero'] using
    m.sPolynomial_monomial_mul f g 0 0 c c

/-- If two generic equations are lifted after multiplying by a common
denominator, the S-polynomial of their lifts maps to the square-scaled
generic S-polynomial. -/
theorem monomialOrder_sPolynomial_map_cleared_pair
    {R : Type u} {F : Type v} [CommRing R] [Field F]
    (φ : R →+* F) (hφ : Function.Injective φ)
    (m : MonomialOrder (Fin 4)) (d : R)
    (p q : MvPolynomial (Fin 4) R)
    (f g : MvPolynomial (Fin 4) F)
    (hp : MvPolynomial.map φ p = MvPolynomial.C (φ d) * f)
    (hq : MvPolynomial.map φ q = MvPolynomial.C (φ d) * g) :
    MvPolynomial.map φ (m.sPolynomial p q) =
      MvPolynomial.C (φ d * φ d) * m.sPolynomial f g := by
  rw [monomialOrder_sPolynomial_map_of_injective φ hφ m p q,
    hp, hq, monomialOrder_sPolynomial_C_mul_same_scalar]

/-- A polynomial lift whose generic image differs by a nonzero scalar has
the same leading exponent as the generic polynomial. -/
theorem monomialOrder_degree_cleared_lift
    {R : Type u} {F : Type v} [CommRing R] [Field F]
    (φ : R →+* F) (hφ : Function.Injective φ)
    (m : MonomialOrder (Fin 4)) (d : R) (hd : d ≠ 0)
    (p : MvPolynomial (Fin 4) R)
    (f : MvPolynomial (Fin 4) F)
    (hp : MvPolynomial.map φ p = MvPolynomial.C (φ d) * f) :
    m.degree p = m.degree f := by
  have hφd : φ d ≠ 0 := by simpa only [map_zero] using hφ.ne hd
  calc
    m.degree p = m.degree (MvPolynomial.map φ p) :=
      (monomialOrder_degree_map_of_injective φ hφ m p).symm
    _ = m.degree (MvPolynomial.C (φ d) * f) := by rw [hp]
    _ = m.degree f := by
      simpa only [smul_eq_C_mul] using
        (m.degree_smul_of_mem_nonZeroDivisors
          (r := φ d) (f := f) (mem_nonZeroDivisors_iff_ne_zero.mpr hφd))

/-- The product of two lifts cleared by the same nonzero scalar has the
same leading exponent as the product of the generic polynomials. -/
theorem monomialOrder_degree_mul_cleared_lifts
    {R : Type u} {F : Type v} [CommRing R] [IsDomain R] [Field F]
    (φ : R →+* F) (hφ : Function.Injective φ)
    (m : MonomialOrder (Fin 4)) (d : R) (hd : d ≠ 0)
    (p q : MvPolynomial (Fin 4) R)
    (f g : MvPolynomial (Fin 4) F)
    (hp : MvPolynomial.map φ p = MvPolynomial.C (φ d) * f)
    (hq : MvPolynomial.map φ q = MvPolynomial.C (φ d) * g) :
    m.degree (p * q) = m.degree (f * g) := by
  apply monomialOrder_degree_cleared_lift φ hφ m (d * d)
    (mul_ne_zero hd hd) (p * q) (f * g)
  simp only [map_mul, hp, hq]
  ring

/-- The S-polynomial of two cleared lifts has the same leading exponent
as the generic S-polynomial. -/
theorem monomialOrder_degree_sPolynomial_cleared_lifts
    {R : Type u} {F : Type v} [CommRing R] [IsDomain R] [Field F]
    (φ : R →+* F) (hφ : Function.Injective φ)
    (m : MonomialOrder (Fin 4)) (d : R) (hd : d ≠ 0)
    (p q : MvPolynomial (Fin 4) R)
    (f g : MvPolynomial (Fin 4) F)
    (hp : MvPolynomial.map φ p = MvPolynomial.C (φ d) * f)
    (hq : MvPolynomial.map φ q = MvPolynomial.C (φ d) * g) :
    m.degree (m.sPolynomial p q) = m.degree (m.sPolynomial f g) := by
  apply monomialOrder_degree_cleared_lift φ hφ m (d * d)
    (mul_ne_zero hd hd) (m.sPolynomial p q) (m.sPolynomial f g)
  simpa only [map_mul] using
    monomialOrder_sPolynomial_map_cleared_pair φ hφ m d p q f g hp hq

end PfaffianDescent
