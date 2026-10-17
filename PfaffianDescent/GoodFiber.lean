import PfaffianDescent.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! The explicit fiber equations in Section 2 of the source note. -/
namespace PfaffianDescent
section
variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- Equations (2.2) on the affine chart of the product of three projective lines. -/
def GoodFiberEquations (u v w : K) : Prop :=
  1 + u * v = 0 ∧ 1 + u * w = 0 ∧ 1 + 2 * v * w = 0

/-- The affine fiber is exactly the quadratic equation in (2.3). -/
theorem goodFiber_iff (u v w : K) :
    GoodFiberEquations u v w ↔ u ^ 2 + 2 = 0 ∧ v = -u⁻¹ ∧ w = -u⁻¹ := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    have hu : u ≠ 0 := by
      intro h
      simp [h] at h₁
    have hv : v = -u⁻¹ := by
      apply (mul_left_cancel₀ hu)
      field_simp
      linear_combination h₁
    have hw : w = -u⁻¹ := by
      apply (mul_left_cancel₀ hu)
      field_simp
      linear_combination h₂
    refine ⟨?_, hv, hw⟩
    linear_combination (u ^ 2) * h₃ - (u * w) * h₁ - (u * v) * h₂ + h₁ + h₂
  · rintro ⟨h, rfl, rfl⟩
    have hu : u ≠ 0 := by
      intro hu
      have htwo : (2 : K) = 0 := by simpa [hu] using h
      exact NeZero.ne (2 : K) htwo
    constructor
    · field_simp
      ring
    constructor
    · field_simp
      ring
    · field_simp
      linear_combination h

omit [NeZero (2 : K)] in
/-- The Jacobian determinant in affine coordinates. -/
theorem goodFiber_jacobian (u v w : K) :
    Matrix.det (!![v, u, 0; w, 0, u; 0, 2*w, 2*v]) = -4*u*v*w := by
  simp only [Matrix.det_fin_three]
  change v*0*(2*v) - v*u*(2*w) - u*w*(2*v) + u*u*0 + 0*w*(2*w) - 0*0*0 = -4*u*v*w
  ring

/-- Every geometric solution of the displayed affine fiber is simple. -/
theorem goodFiber_jacobian_ne_zero (u v w : K) (h : GoodFiberEquations u v w) :
    Matrix.det (!![v, u, 0; w, 0, u; 0, 2*w, 2*v]) ≠ 0 := by
  have hu : u ≠ 0 := by intro hu; simpa [hu] using h.1
  have hv : v ≠ 0 := by intro hv; simpa [hv] using h.1
  have hw : w ≠ 0 := by intro hw; simpa [hw] using h.2.1
  rw [goodFiber_jacobian]
  have hfour : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero (NeZero.ne (2 : K)) (NeZero.ne (2 : K))
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hfour) hu) hv) hw

/-- There are no points of the displayed projective fiber outside the affine chart. -/
theorem goodFiber_affine_chart (a b : Fin 3 → K)
    (hne : ∀ i, a i ≠ 0 ∨ b i ≠ 0)
    (h₁ : a 0 * a 1 + b 0 * b 1 = 0)
    (h₂ : a 0 * a 2 + b 0 * b 2 = 0)
    (h₃ : a 1 * a 2 + 2 * b 1 * b 2 = 0) : ∀ i, a i ≠ 0 := by
  have ha₀ : a 0 ≠ 0 := by
    intro hz
    have hb₀ := (hne 0).resolve_left (not_not_intro hz)
    have hb₁ : b 1 = 0 := by
      apply (mul_eq_zero.mp (by simpa [hz] using h₁)).resolve_left hb₀
    have hb₂ : b 2 = 0 := by
      apply (mul_eq_zero.mp (by simpa [hz] using h₂)).resolve_left hb₀
    have ha₁ := (hne 1).resolve_right (not_not_intro hb₁)
    have ha₂ := (hne 2).resolve_right (not_not_intro hb₂)
    exact (mul_ne_zero ha₁ ha₂) (by simpa [hb₁, hb₂] using h₃)
  have ha₁ : a 1 ≠ 0 := by
    intro hz
    have hb₁ := (hne 1).resolve_left (not_not_intro hz)
    have hb₀ : b 0 = 0 := by
      exact (mul_eq_zero.mp (by simpa [hz] using h₁)).resolve_right hb₁
    have hb₂ : b 2 = 0 := by
      have hh : (2 * b 1) * b 2 = 0 := by simpa [hz] using h₃
      exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (NeZero.ne (2 : K)) hb₁)
    have ha₂ := (hne 2).resolve_right (not_not_intro hb₂)
    exact (mul_ne_zero ha₀ ha₂) (by simpa [hb₀] using h₂)
  have ha₂ : a 2 ≠ 0 := by
    intro hz
    have hb₂ := (hne 2).resolve_left (not_not_intro hz)
    have hb₀ : b 0 = 0 := by
      exact (mul_eq_zero.mp (by simpa [hz] using h₂)).resolve_right hb₂
    exact (mul_ne_zero ha₀ ha₁) (by simpa [hb₀] using h₁)
  intro i
  fin_cases i
  · exact ha₀
  · exact ha₁
  · exact ha₂

end
end PfaffianDescent
