import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-! Exact field-degree scaled OWN genus window; no geometric bound is an input. -/
namespace PfaffianDescent.Coray

/-- The arithmetic genus triangular term is kept in an exact twice form,
so native integer Euler bounds can be compared without division roundoff. -/
theorem coray_twice_chooseGenus_polynomial001 (lambda : ℕ) :
    2 * (1 + 3 * lambda.choose 2) = 2 + 3 * lambda * (lambda - 1) := by
  have h : 2 * lambda.choose 2 = lambda * (lambda - 1) := by
    have hd := Nat.descFactorial_eq_factorial_mul_choose lambda 2
    rw [show Nat.factorial 2 = 2 by decide] at hd
    simpa only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
      mul_one, mul_comm] using hd.symm
  calc
    _ = 2 + 3 * (2 * lambda.choose 2) := by ring
    _ = _ := by rw [h]; ring

/-- A genuine field degree r>=2 and r*lambda<=n make the scaled OWN genus
strictly smaller than every original degree in the Coray lower window.
Neither an incidence count nor a desired defect/regularity premise occurs. -/
theorem coray_modelField_scaledOwnGenus_lt_originalDegree001
    (r lambda n d : ℕ) (hr : 2 ≤ r) (hlambda : 1 ≤ lambda)
    (hDegree : r * lambda ≤ n) (hWindow : 1 + 3 * n.choose 2 ≤ d) :
    r * (1 + 3 * lambda.choose 2) < d := by
  have hrQ : (2 : ℚ) ≤ (r : ℚ) := by exact_mod_cast hr
  have hlambdaQ : (1 : ℚ) ≤ (lambda : ℚ) := by exact_mod_cast hlambda
  have hSquare : (1 : ℚ) ≤ (lambda : ℚ) ^ 2 := by nlinarith
  have hProduct : (2 : ℚ) ≤ (r : ℚ) * (lambda : ℚ) ^ 2 := by
    calc
      (2 : ℚ) ≤ r := hrQ
      _ = (r : ℚ) * 1 := by ring
      _ ≤ (r : ℚ) * (lambda : ℚ) ^ 2 :=
        mul_le_mul_of_nonneg_left hSquare (by positivity)
  have hFactor : 0 < ((r : ℚ) - 1) *
      (3 * (r : ℚ) * (lambda : ℚ) ^ 2 - 2) :=
    mul_pos (by linarith) (by nlinarith)
  have hIdentity : (2 : ℚ) * (1 + 3 * ((r * lambda).choose 2 : ℚ)) -
      2 * (r : ℚ) * (1 + 3 * (lambda.choose 2 : ℚ)) =
        ((r : ℚ) - 1) * (3 * (r : ℚ) * (lambda : ℚ) ^ 2 - 2) := by
    rw [Nat.cast_choose_two ℚ (r * lambda), Nat.cast_choose_two ℚ lambda]
    push_cast
    ring
  have hStrictQ : (r : ℚ) * (1 + 3 * (lambda.choose 2 : ℚ)) <
      1 + 3 * ((r * lambda).choose 2 : ℚ) := by linarith
  have hStrict : r * (1 + 3 * lambda.choose 2) <
      1 + 3 * (r * lambda).choose 2 := by exact_mod_cast hStrictQ
  have hChoose : (r * lambda).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 hDegree
  exact hStrict.trans_le ((Nat.add_le_add_left (Nat.mul_le_mul_left 3 hChoose) 1).trans hWindow)

end PfaffianDescent.Coray
