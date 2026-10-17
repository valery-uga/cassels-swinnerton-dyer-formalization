import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PfaffianDescent

lemma six_mul_choose_three (d : ℕ) :
    6 * (d+3).choose 3 = (d+3) * (d+2) * (d+1) := by
  have h2 := Nat.add_one_mul_choose_eq (d+1) 1
  have h3 := Nat.add_one_mul_choose_eq (d+2) 2
  simp only [Nat.choose_one_right] at h2
  have h := congrArg (fun t => (d+3)*t) h2
  nlinarith

/-- The Hilbert numerator identity in the dimensions needed for middle exactness. -/
lemma frame_dimension_identity (d : ℕ) :
    5 * (d+6).choose 3 + 5 + (d+3).choose 3 =
      5 * (d+5).choose 3 + (d+8).choose 3 := by
  have h0 := six_mul_choose_three d
  have h2 := six_mul_choose_three (d+2)
  have h3 := six_mul_choose_three (d+3)
  have h5 := six_mul_choose_three (d+5)
  simp only [Nat.add_assoc] at h2 h3 h5
  nlinarith

end PfaffianDescent
