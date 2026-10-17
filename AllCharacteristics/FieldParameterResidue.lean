import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Nonzero equations at field-valued parameters

The image of the unique point of a field spectrum is the kernel of its
coefficient homomorphism. Reducing a polynomial to the residue field of this
point detects zero exactly as mapping its coefficients to the given field.
-/

open AlgebraicGeometry
namespace AllCharacteristics
universe u v w
attribute [local instance] PrimeSpectrum.isPrime

/-- The prime ideal corresponding to a field-valued point is exactly the
kernel of its ring homomorphism. -/
theorem fieldPoint_asIdeal_eq_ker
    {R : Type u} {k : Type v} [CommRing R] [Field k] (b : R →+* k) :
    (PrimeSpectrum.comap b (IsLocalRing.closedPoint k)).asIdeal = RingHom.ker b := by
  ext r
  change b r ∈ IsLocalRing.maximalIdeal k ↔ b r = 0
  rw [IsLocalRing.maximalIdeal_eq_bot]
  rfl

/-- Nonzeroness over the residue field of a parameter agrees with nonzeroness
over any field realizing that parameter. -/
theorem mvPolynomial_residue_map_ne_zero_iff_field_map
    {R : Type u} {k : Type v} {σ : Type w} [CommRing R] [Field k]
    (b : R →+* k) (y : PrimeSpectrum R) (hy : y.asIdeal = RingHom.ker b)
    (p : MvPolynomial σ R) :
    p.map (algebraMap R y.asIdeal.ResidueField) ≠ 0 ↔ p.map b ≠ 0 := by
  apply not_congr
  simp only [MvPolynomial.ext_iff, MvPolynomial.coeff_map, MvPolynomial.coeff_zero,
    Ideal.algebraMap_residueField_eq_zero]
  rw [hy]
  rfl

end AllCharacteristics
