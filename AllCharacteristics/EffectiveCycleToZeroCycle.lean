import AllCharacteristics.CycleDegrees

/-!
# Effective cycles as signed zero-cycles

Passing from natural multiplicities to integer multiplicities preserves the
actual scheme degree. This connects finite-scheme fundamental cycles with the
Bézout argument for signed degree-one cycles.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- Regard an effective cycle as an integer zero-cycle. -/
noncomputable def EffectiveZeroCycle.toZeroCycle {X : Scheme.{u}}
    (z : EffectiveZeroCycle X) : ZeroCycle X :=
  z.mapRange (fun n : ℕ ↦ (n : ℤ)) (Nat.cast_zero)

/-- Passing to integer coefficients preserves the degree. -/
theorem EffectiveZeroCycle.degree_toZeroCycle
    {X Y : Scheme.{u}} (f : X ⟶ Y) (z : EffectiveZeroCycle X) :
    ZeroCycle.degree f z.toZeroCycle = (EffectiveZeroCycle.degree f z : ℤ) := by
  change (z.mapRange (fun n : ℕ ↦ (n : ℤ)) (Nat.cast_zero)).sum
      (fun x n ↦ n * (f.residueDegree x.1 : ℤ)) =
    ((z.sum (fun x n ↦ n * f.residueDegree x.1) : ℕ) : ℤ)
  rw [Finsupp.sum_mapRange_index (fun _ ↦ zero_mul _)]
  simp only [Finsupp.sum, Nat.cast_sum, Nat.cast_mul]

end AllCharacteristics
