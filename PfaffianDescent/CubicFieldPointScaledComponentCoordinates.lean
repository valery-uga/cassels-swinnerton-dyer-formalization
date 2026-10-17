import PfaffianDescent.CubicFieldPointComponentCoordinates

/-! Scaling the homogeneous coordinates of an actual field component
preserves the literal affine chart ratios. -/

noncomputable section
namespace PfaffianDescent

universe u

theorem cubicFieldPoint_scaled_coordinate_ratios
    {E : Type u} [Field E] (x y : Fin 4 → E) (s : E)
    (hs : s ≠ 0) (hy : ∀ r, y r = s * x r)
    (j : Fin 4) (hxj : x j ≠ 0) :
    y j ≠ 0 ∧ ∀ r, (y j)⁻¹ * y r = (x j)⁻¹ * x r := by
  refine ⟨by rw [hy]; exact mul_ne_zero hs hxj, ?_⟩
  intro r
  rw [hy, hy, mul_inv_rev]
  calc
    (x j)⁻¹ * s⁻¹ * (s * x r) = (x j)⁻¹ * (s⁻¹ * s) * x r := by ring
    _ = (x j)⁻¹ * x r := by rw [inv_mul_cancel₀ hs, mul_one]

end PfaffianDescent
