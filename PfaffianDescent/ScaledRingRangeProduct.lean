import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.Ring

/-! Products of literal scaled images of a ring homomorphism.
The actual ring multiplication supplies every product and every target
coefficient; no product-image or valuation certificate is assumed.
SOURCE ONLY / UNVERIFIED. -/
namespace PfaffianDescent

/-- The product of two literal scaled ring images is the literal image
scaled by their product. The reverse direction uses the original 1. -/
theorem ringHom_scaledRangeProduct
    {R F : Type*} [CommRing R] [CommRing F]
    (κ : R →+* F) (u v : F) :
    Set.range (fun p : R × R => (κ p.1 * u) * (κ p.2 * v)) =
      Set.range (fun r : R => κ r * (u * v)) := by
  have hvalue (r s : R) : (κ r * u) * (κ s * v) = κ (r * s) * (u * v) := by
    rw [κ.map_mul]
    ring
  apply Set.Subset.antisymm
  · rintro f ⟨p, hp⟩
    exact ⟨p.1 * p.2, (hvalue p.1 p.2).symm.trans hp⟩
  · rintro f ⟨r, hr⟩
    exact ⟨⟨r, 1⟩, (hvalue r 1).trans
      ((congrArg (fun s : R => κ s * (u * v)) (mul_one r)).trans hr)⟩

/-- Integer exponents add for the product of the SAME literal scaled
ring image in a field. The sole nonzero input is the actual scale z. -/
theorem ringHom_scaledRangeProduct_zpow
    {R F : Type*} [CommRing R] [Field F]
    (κ : R →+* F) (z : F) (hz : z ≠ 0) (a b : ℤ) :
    Set.range (fun p : R × R => (κ p.1 * z ^ a) * (κ p.2 * z ^ b)) =
      Set.range (fun r : R => κ r * z ^ (a + b)) :=
  (ringHom_scaledRangeProduct κ (z ^ a) (z ^ b)).trans
    (congrArg (fun v : F => Set.range (fun r : R => κ r * v))
      (zpow_add₀ hz a b).symm)

end PfaffianDescent
