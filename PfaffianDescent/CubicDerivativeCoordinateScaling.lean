import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.Pi

/-! Nonzero chart normalization scales the three derivative fibres by
units, so it preserves the full six-dimensional derivative span. -/

noncomputable section
namespace PfaffianDescent

universe u

def cubicDerivativeCoordinateScaleEquiv
    {E : Type u} [Field E] (a : Fin 3 → E) (ha : ∀ i, a i ≠ 0) :
    (Fin 3 → Fin 2 → E) ≃ₗ[E] (Fin 3 → Fin 2 → E) where
  toFun v := fun i => a i • v i
  invFun v := fun i => (a i)⁻¹ • v i
  left_inv v := by
    funext i
    change (a i)⁻¹ • (a i • v i) = v i
    rw [smul_smul, inv_mul_cancel₀ (ha i), one_smul]
  right_inv v := by
    funext i
    change a i • ((a i)⁻¹ • v i) = v i
    rw [smul_smul, mul_inv_cancel₀ (ha i), one_smul]
  map_add' v w := by
    funext i
    exact smul_add (a i) (v i) (w i)
  map_smul' c v := by
    funext i
    exact smul_comm (a i) c (v i)

theorem cubicDerivativeCoordinateScale_span_top
    {E : Type u} [Field E] {ι : Type*}
    (a : Fin 3 → E) (ha : ∀ i, a i ≠ 0)
    (v : ι → Fin 3 → Fin 2 → E)
    (hv : Submodule.span E (Set.range v) = ⊤) :
    Submodule.span E (Set.range (fun k => fun i => a i • v k i)) = ⊤ := by
  let e := cubicDerivativeCoordinateScaleEquiv a ha
  have h := congrArg (Submodule.map e.toLinearMap) hv
  rw [Submodule.map_span, ← Set.range_comp', Submodule.map_top,
    LinearMap.range_eq_top.mpr e.surjective] at h
  exact h

end PfaffianDescent
