import Mathlib.Tactic

/-! Arithmetic consequences of the original ideal-grade increment bound.
The initial grade and recurrence remain explicit hypotheses here; this is
not an identification of native cohomology with a Hilbert polynomial. -/
namespace PfaffianDescent.Coray

theorem idealGrade_eq_zero_below_third_degree
    (a : ℕ → ℕ) (r : ℕ) (hzero : a 0 = 0)
    (hstep : ∀ d, a (d + 1) ≤ a d +
      (if 3 * (d + 1) = 3 * r then 1 else 3 * (d + 1) - 3 * r))
    (t : ℕ) (ht : t < r) : a t = 0 := by
  induction t with
  | zero => exact hzero
  | succ t ih =>
    have hprev : a t = 0 := ih (by omega)
    have hne : 3 * (t + 1) ≠ 3 * r := by omega
    have hsub : 3 * (t + 1) - 3 * r = 0 := by omega
    have h := hstep t
    rw [if_neg hne, hsub, hprev] at h
    omega

theorem idealGrade_le_one_at_third_degree
    (a : ℕ → ℕ) (r : ℕ) (hzero : a 0 = 0)
    (hstep : ∀ d, a (d + 1) ≤ a d +
      (if 3 * (d + 1) = 3 * r then 1 else 3 * (d + 1) - 3 * r)) :
    a r ≤ 1 := by
  cases r with
  | zero => omega
  | succ r =>
    have hprev := idealGrade_eq_zero_below_third_degree a (r + 1)
      hzero hstep r (by omega)
    have h := hstep r
    rw [if_pos rfl, hprev] at h
    exact h

theorem idealGrade_twice_le_quadratic_above_third_degree
    (a : ℕ → ℕ) (r : ℕ) (hzero : a 0 = 0)
    (hstep : ∀ d, a (d + 1) ≤ a d +
      (if 3 * (d + 1) = 3 * r then 1 else 3 * (d + 1) - 3 * r))
    (s : ℕ) : 2 * a (r + s) ≤ 2 + 3 * s * (s + 1) := by
  induction s with
  | zero =>
    have h := idealGrade_le_one_at_third_degree a r hzero hstep
    simpa using (Nat.mul_le_mul_left 2 h)
  | succ s ih =>
    have hne : 3 * (r + s + 1) ≠ 3 * r := by omega
    have hsub : 3 * (r + s + 1) - 3 * r = 3 * (s + 1) := by omega
    have h := hstep (r + s)
    rw [if_neg hne, hsub] at h
    have hnext : a (r + (s + 1)) ≤ a (r + s) + 3 * (s + 1) := by
      simpa only [Nat.add_assoc] using h
    nlinarith

theorem idealGrade_le_quadratic_above_third_degree
    (a : ℕ → ℕ) (r : ℕ) (hzero : a 0 = 0)
    (hstep : ∀ d, a (d + 1) ≤ a d +
      (if 3 * (d + 1) = 3 * r then 1 else 3 * (d + 1) - 3 * r))
    (s : ℕ) : a (r + s) ≤ 1 + 3 * s * (s + 1) / 2 := by
  have h := idealGrade_twice_le_quadratic_above_third_degree a r hzero hstep s
  omega

end PfaffianDescent.Coray
