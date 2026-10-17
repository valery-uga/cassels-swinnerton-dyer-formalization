import PfaffianDescent.VoisinIntrinsicIdealRatioFamilies
import PfaffianDescent.VoisinQuadraticEvaluationMatrix

/-! A nonzero rescaling of each labeled point preserves every selected
quadratic evaluation minor. -/

namespace PfaffianDescent

open MvPolynomial AllCharacteristics.UniversalHomogeneous

universe u

theorem eightPointQuadraticEvaluationMinor_isUnit_det_iff_of_ratioFamilies
    {F : Type u} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (x y : Fin 8 → Fin 4 → F)
    (j : Fin 8 → Fin 4)
    (hxj : ∀ k, x k (j k) ≠ 0)
    (hratio : ∀ k i,
      (y k (j k))⁻¹ * y k i = (x k (j k))⁻¹ * x k i) :
    IsUnit (eightPointQuadraticEvaluationMinor m y).det ↔
      IsUnit (eightPointQuadraticEvaluationMinor m x).det := by
  have hyj : ∀ k, y k (j k) ≠ 0 := by
    intro k hk
    have h := hratio k (j k)
    simp [hk, hxj k] at h
  let a : Fin 8 → F := fun k => y k (j k) / x k (j k)
  have ha : ∀ k, a k ≠ 0 := by
    intro k
    exact div_ne_zero (hyj k) (hxj k)
  let u : Fin 8 → Fˣ := fun k => Units.mk0 (a k) (ha k)
  have hscale : y = fun k i => (u k : F) * x k i := by
    funext k i
    calc
      y k i = y k (j k) * ((y k (j k))⁻¹ * y k i) := by simp [hyj k]
      _ = y k (j k) * ((x k (j k))⁻¹ * x k i) := by rw [hratio k i]
      _ = (u k : F) * x k i := by
        simp only [u, a, Units.val_mk0, div_eq_mul_inv, mul_assoc]
  rw [hscale]
  exact eightPointQuadraticEvaluationMinor_isUnit_det_scale_iff m u x

end PfaffianDescent
