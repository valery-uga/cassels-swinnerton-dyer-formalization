import PfaffianDescent.Basic

/-! The Pfaffian adjugate identity, split into entries to respect default limits. -/
namespace PfaffianDescent
section Ring
variable {R : Type*} [CommRing R]

/-- The quadratic Pfaffian adjugate of a six by six alternating matrix. -/
def copf6 (A : Mat R 6) : Mat R 6 :=
  !![0, -(A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4), (A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4), -(A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4), (A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3), -(A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3);
    (A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4), 0, -(A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4), (A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4), -(A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3), (A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3);
    -(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4), (A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4), 0, -(A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4), (A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3), -(A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3);
    (A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4), -(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4), (A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4), 0, -(A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2), (A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2);
    -(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3), (A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3), -(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3), (A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2), 0, -(A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2);
    (A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3), -(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3), (A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3), -(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2), (A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2), 0]

private theorem copf6_mul_entry_0_0 (A : Mat R 6) :
    (copf6 A * skew6 A) 0 0 = pf6 A := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * 0 + ((-(A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)) * (-A 0 1) + (((A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) * (-A 0 2) + ((-(A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)) * (-A 0 3) + (((A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) * (-A 0 4) + ((-(A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)) * (-A 0 5)))))) = pf6 A
  unfold pf6
  ring

private theorem copf6_mul_entry_0_1 (A : Mat R 6) :
    (copf6 A * skew6 A) 0 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * A 0 1 + ((-(A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)) * 0 + (((A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) * (-A 1 2) + ((-(A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)) * (-A 1 3) + (((A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) * (-A 1 4) + ((-(A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)) * (-A 1 5)))))) = 0
  ring

private theorem copf6_mul_entry_0_2 (A : Mat R 6) :
    (copf6 A * skew6 A) 0 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * A 0 2 + ((-(A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)) * A 1 2 + (((A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) * 0 + ((-(A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)) * (-A 2 3) + (((A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) * (-A 2 4) + ((-(A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)) * (-A 2 5)))))) = 0
  ring

private theorem copf6_mul_entry_0_3 (A : Mat R 6) :
    (copf6 A * skew6 A) 0 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * A 0 3 + ((-(A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)) * A 1 3 + (((A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) * A 2 3 + ((-(A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)) * 0 + (((A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) * (-A 3 4) + ((-(A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)) * (-A 3 5)))))) = 0
  ring

private theorem copf6_mul_entry_0_4 (A : Mat R 6) :
    (copf6 A * skew6 A) 0 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * A 0 4 + ((-(A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)) * A 1 4 + (((A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) * A 2 4 + ((-(A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)) * A 3 4 + (((A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) * 0 + ((-(A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)) * (-A 4 5)))))) = 0
  ring

private theorem copf6_mul_entry_0_5 (A : Mat R 6) :
    (copf6 A * skew6 A) 0 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * A 0 5 + ((-(A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)) * A 1 5 + (((A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) * A 2 5 + ((-(A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)) * A 3 5 + (((A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) * A 4 5 + ((-(A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)) * 0))))) = 0
  ring

private theorem copf6_mul_entry_1_0 (A : Mat R 6) :
    (copf6 A * skew6 A) 1 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)) * 0 + ((0) * (-A 0 1) + ((-(A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4)) * (-A 0 2) + (((A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) * (-A 0 3) + ((-(A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3)) * (-A 0 4) + (((A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) * (-A 0 5)))))) = 0
  ring

private theorem copf6_mul_entry_1_1 (A : Mat R 6) :
    (copf6 A * skew6 A) 1 1 = pf6 A := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)) * A 0 1 + ((0) * 0 + ((-(A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4)) * (-A 1 2) + (((A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) * (-A 1 3) + ((-(A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3)) * (-A 1 4) + (((A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) * (-A 1 5)))))) = pf6 A
  unfold pf6
  ring

private theorem copf6_mul_entry_1_2 (A : Mat R 6) :
    (copf6 A * skew6 A) 1 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)) * A 0 2 + ((0) * A 1 2 + ((-(A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4)) * 0 + (((A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) * (-A 2 3) + ((-(A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3)) * (-A 2 4) + (((A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) * (-A 2 5)))))) = 0
  ring

private theorem copf6_mul_entry_1_3 (A : Mat R 6) :
    (copf6 A * skew6 A) 1 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)) * A 0 3 + ((0) * A 1 3 + ((-(A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4)) * A 2 3 + (((A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) * 0 + ((-(A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3)) * (-A 3 4) + (((A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) * (-A 3 5)))))) = 0
  ring

private theorem copf6_mul_entry_1_4 (A : Mat R 6) :
    (copf6 A * skew6 A) 1 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)) * A 0 4 + ((0) * A 1 4 + ((-(A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4)) * A 2 4 + (((A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) * A 3 4 + ((-(A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3)) * 0 + (((A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) * (-A 4 5)))))) = 0
  ring

private theorem copf6_mul_entry_1_5 (A : Mat R 6) :
    (copf6 A * skew6 A) 1 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4)) * A 0 5 + ((0) * A 1 5 + ((-(A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4)) * A 2 5 + (((A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) * A 3 5 + ((-(A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3)) * A 4 5 + (((A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) * 0))))) = 0
  ring

private theorem copf6_mul_entry_2_0 (A : Mat R 6) :
    (copf6 A * skew6 A) 2 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) * 0 + (((A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4)) * (-A 0 1) + ((0) * (-A 0 2) + ((-(A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4)) * (-A 0 3) + (((A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) * (-A 0 4) + ((-(A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3)) * (-A 0 5)))))) = 0
  ring

private theorem copf6_mul_entry_2_1 (A : Mat R 6) :
    (copf6 A * skew6 A) 2 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) * A 0 1 + (((A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4)) * 0 + ((0) * (-A 1 2) + ((-(A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4)) * (-A 1 3) + (((A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) * (-A 1 4) + ((-(A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3)) * (-A 1 5)))))) = 0
  ring

private theorem copf6_mul_entry_2_2 (A : Mat R 6) :
    (copf6 A * skew6 A) 2 2 = pf6 A := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) * A 0 2 + (((A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4)) * A 1 2 + ((0) * 0 + ((-(A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4)) * (-A 2 3) + (((A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) * (-A 2 4) + ((-(A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3)) * (-A 2 5)))))) = pf6 A
  unfold pf6
  ring

private theorem copf6_mul_entry_2_3 (A : Mat R 6) :
    (copf6 A * skew6 A) 2 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) * A 0 3 + (((A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4)) * A 1 3 + ((0) * A 2 3 + ((-(A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4)) * 0 + (((A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) * (-A 3 4) + ((-(A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3)) * (-A 3 5)))))) = 0
  ring

private theorem copf6_mul_entry_2_4 (A : Mat R 6) :
    (copf6 A * skew6 A) 2 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) * A 0 4 + (((A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4)) * A 1 4 + ((0) * A 2 4 + ((-(A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4)) * A 3 4 + (((A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) * 0 + ((-(A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3)) * (-A 4 5)))))) = 0
  ring

private theorem copf6_mul_entry_2_5 (A : Mat R 6) :
    (copf6 A * skew6 A) 2 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4)) * A 0 5 + (((A 0 3 * A 4 5 - A 0 4 * A 3 5 + A 0 5 * A 3 4)) * A 1 5 + ((0) * A 2 5 + ((-(A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4)) * A 3 5 + (((A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) * A 4 5 + ((-(A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3)) * 0))))) = 0
  ring

private theorem copf6_mul_entry_3_0 (A : Mat R 6) :
    (copf6 A * skew6 A) 3 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)) * 0 + ((-(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) * (-A 0 1) + (((A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4)) * (-A 0 2) + ((0) * (-A 0 3) + ((-(A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2)) * (-A 0 4) + (((A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) * (-A 0 5)))))) = 0
  ring

private theorem copf6_mul_entry_3_1 (A : Mat R 6) :
    (copf6 A * skew6 A) 3 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)) * A 0 1 + ((-(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) * 0 + (((A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4)) * (-A 1 2) + ((0) * (-A 1 3) + ((-(A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2)) * (-A 1 4) + (((A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) * (-A 1 5)))))) = 0
  ring

private theorem copf6_mul_entry_3_2 (A : Mat R 6) :
    (copf6 A * skew6 A) 3 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)) * A 0 2 + ((-(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) * A 1 2 + (((A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4)) * 0 + ((0) * (-A 2 3) + ((-(A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2)) * (-A 2 4) + (((A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) * (-A 2 5)))))) = 0
  ring

private theorem copf6_mul_entry_3_3 (A : Mat R 6) :
    (copf6 A * skew6 A) 3 3 = pf6 A := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)) * A 0 3 + ((-(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) * A 1 3 + (((A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4)) * A 2 3 + ((0) * 0 + ((-(A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2)) * (-A 3 4) + (((A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) * (-A 3 5)))))) = pf6 A
  unfold pf6
  ring

private theorem copf6_mul_entry_3_4 (A : Mat R 6) :
    (copf6 A * skew6 A) 3 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)) * A 0 4 + ((-(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) * A 1 4 + (((A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4)) * A 2 4 + ((0) * A 3 4 + ((-(A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2)) * 0 + (((A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) * (-A 4 5)))))) = 0
  ring

private theorem copf6_mul_entry_3_5 (A : Mat R 6) :
    (copf6 A * skew6 A) 3 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4)) * A 0 5 + ((-(A 0 2 * A 4 5 - A 0 4 * A 2 5 + A 0 5 * A 2 4)) * A 1 5 + (((A 0 1 * A 4 5 - A 0 4 * A 1 5 + A 0 5 * A 1 4)) * A 2 5 + ((0) * A 3 5 + ((-(A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2)) * A 4 5 + (((A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) * 0))))) = 0
  ring

private theorem copf6_mul_entry_4_0 (A : Mat R 6) :
    (copf6 A * skew6 A) 4 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) * 0 + (((A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3)) * (-A 0 1) + ((-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) * (-A 0 2) + (((A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2)) * (-A 0 3) + ((0) * (-A 0 4) + ((-(A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2)) * (-A 0 5)))))) = 0
  ring

private theorem copf6_mul_entry_4_1 (A : Mat R 6) :
    (copf6 A * skew6 A) 4 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) * A 0 1 + (((A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3)) * 0 + ((-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) * (-A 1 2) + (((A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2)) * (-A 1 3) + ((0) * (-A 1 4) + ((-(A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2)) * (-A 1 5)))))) = 0
  ring

private theorem copf6_mul_entry_4_2 (A : Mat R 6) :
    (copf6 A * skew6 A) 4 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) * A 0 2 + (((A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3)) * A 1 2 + ((-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) * 0 + (((A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2)) * (-A 2 3) + ((0) * (-A 2 4) + ((-(A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2)) * (-A 2 5)))))) = 0
  ring

private theorem copf6_mul_entry_4_3 (A : Mat R 6) :
    (copf6 A * skew6 A) 4 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) * A 0 3 + (((A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3)) * A 1 3 + ((-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) * A 2 3 + (((A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2)) * 0 + ((0) * (-A 3 4) + ((-(A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2)) * (-A 3 5)))))) = 0
  ring

private theorem copf6_mul_entry_4_4 (A : Mat R 6) :
    (copf6 A * skew6 A) 4 4 = pf6 A := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) * A 0 4 + (((A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3)) * A 1 4 + ((-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) * A 2 4 + (((A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2)) * A 3 4 + ((0) * 0 + ((-(A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2)) * (-A 4 5)))))) = pf6 A
  unfold pf6
  ring

private theorem copf6_mul_entry_4_5 (A : Mat R 6) :
    (copf6 A * skew6 A) 4 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3)) * A 0 5 + (((A 0 2 * A 3 5 - A 0 3 * A 2 5 + A 0 5 * A 2 3)) * A 1 5 + ((-(A 0 1 * A 3 5 - A 0 3 * A 1 5 + A 0 5 * A 1 3)) * A 2 5 + (((A 0 1 * A 2 5 - A 0 2 * A 1 5 + A 0 5 * A 1 2)) * A 3 5 + ((0) * A 4 5 + ((-(A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2)) * 0))))) = 0
  ring

private theorem copf6_mul_entry_5_0 (A : Mat R 6) :
    (copf6 A * skew6 A) 5 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)) * 0 + ((-(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) * (-A 0 1) + (((A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3)) * (-A 0 2) + ((-(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) * (-A 0 3) + (((A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2)) * (-A 0 4) + ((0) * (-A 0 5)))))) = 0
  ring

private theorem copf6_mul_entry_5_1 (A : Mat R 6) :
    (copf6 A * skew6 A) 5 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)) * A 0 1 + ((-(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) * 0 + (((A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3)) * (-A 1 2) + ((-(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) * (-A 1 3) + (((A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2)) * (-A 1 4) + ((0) * (-A 1 5)))))) = 0
  ring

private theorem copf6_mul_entry_5_2 (A : Mat R 6) :
    (copf6 A * skew6 A) 5 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)) * A 0 2 + ((-(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) * A 1 2 + (((A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3)) * 0 + ((-(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) * (-A 2 3) + (((A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2)) * (-A 2 4) + ((0) * (-A 2 5)))))) = 0
  ring

private theorem copf6_mul_entry_5_3 (A : Mat R 6) :
    (copf6 A * skew6 A) 5 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)) * A 0 3 + ((-(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) * A 1 3 + (((A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3)) * A 2 3 + ((-(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) * 0 + (((A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2)) * (-A 3 4) + ((0) * (-A 3 5)))))) = 0
  ring

private theorem copf6_mul_entry_5_4 (A : Mat R 6) :
    (copf6 A * skew6 A) 5 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)) * A 0 4 + ((-(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) * A 1 4 + (((A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3)) * A 2 4 + ((-(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) * A 3 4 + (((A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2)) * 0 + ((0) * (-A 4 5)))))) = 0
  ring

private theorem copf6_mul_entry_5_5 (A : Mat R 6) :
    (copf6 A * skew6 A) 5 5 = pf6 A := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3)) * A 0 5 + ((-(A 0 2 * A 3 4 - A 0 3 * A 2 4 + A 0 4 * A 2 3)) * A 1 5 + (((A 0 1 * A 3 4 - A 0 3 * A 1 4 + A 0 4 * A 1 3)) * A 2 5 + ((-(A 0 1 * A 2 4 - A 0 2 * A 1 4 + A 0 4 * A 1 2)) * A 3 5 + (((A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2)) * A 4 5 + ((0) * 0))))) = pf6 A
  unfold pf6
  ring

theorem copf6_mul_skew6 (A : Mat R 6) :
    copf6 A * skew6 A = pf6 A • (1 : Mat R 6) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using copf6_mul_entry_0_0 A
  · simpa using copf6_mul_entry_0_1 A
  · simpa using copf6_mul_entry_0_2 A
  · simpa using copf6_mul_entry_0_3 A
  · simpa using copf6_mul_entry_0_4 A
  · simpa using copf6_mul_entry_0_5 A
  · simpa using copf6_mul_entry_1_0 A
  · simpa using copf6_mul_entry_1_1 A
  · simpa using copf6_mul_entry_1_2 A
  · simpa using copf6_mul_entry_1_3 A
  · simpa using copf6_mul_entry_1_4 A
  · simpa using copf6_mul_entry_1_5 A
  · simpa using copf6_mul_entry_2_0 A
  · simpa using copf6_mul_entry_2_1 A
  · simpa using copf6_mul_entry_2_2 A
  · simpa using copf6_mul_entry_2_3 A
  · simpa using copf6_mul_entry_2_4 A
  · simpa using copf6_mul_entry_2_5 A
  · simpa using copf6_mul_entry_3_0 A
  · simpa using copf6_mul_entry_3_1 A
  · simpa using copf6_mul_entry_3_2 A
  · simpa using copf6_mul_entry_3_3 A
  · simpa using copf6_mul_entry_3_4 A
  · simpa using copf6_mul_entry_3_5 A
  · simpa using copf6_mul_entry_4_0 A
  · simpa using copf6_mul_entry_4_1 A
  · simpa using copf6_mul_entry_4_2 A
  · simpa using copf6_mul_entry_4_3 A
  · simpa using copf6_mul_entry_4_4 A
  · simpa using copf6_mul_entry_4_5 A
  · simpa using copf6_mul_entry_5_0 A
  · simpa using copf6_mul_entry_5_1 A
  · simpa using copf6_mul_entry_5_2 A
  · simpa using copf6_mul_entry_5_3 A
  · simpa using copf6_mul_entry_5_4 A
  · simpa using copf6_mul_entry_5_5 A

theorem copf6_mul (A : Mat R 6) (hA : IsAlternating A) :
    copf6 A * A = pf6 A • (1 : Mat R 6) := by
  simpa only [skew6_eq A hA] using copf6_mul_skew6 A

end Ring

section Domain
variable {K : Type*} [CommRing K] [IsDomain K]

/-- The precise singular-matrix implication used in the arithmetic argument.
It does not require expanding a six by six determinant. -/
theorem pf6_eq_zero_of_kernel (A : Mat K 6) (hA : IsAlternating A)
    (v : Vec K 6) (hv : v ≠ 0) (hAv : A.mulVec v = 0) : pf6 A = 0 := by
  have h := congrArg (fun M : Mat K 6 => M.mulVec v) (copf6_mul A hA)
  rw [← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_zero, Matrix.smul_mulVec,
    Matrix.one_mulVec] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hv

end Domain
end PfaffianDescent
