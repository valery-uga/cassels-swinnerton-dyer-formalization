import PfaffianDescent.Trivector
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.FieldSimp

/-! The square system consisting of eighteen contraction equations and two fixed coordinates. -/
namespace PfaffianDescent
section Ring
variable {R : Type*} [CommRing R]

/-- Eighteen contraction equations, with coordinates 13 and 14 completing the system. -/
private def constraintMatrixDataRow_0 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![A 0 1 2, A 0 1 3, A 0 1 4, A 0 1 5, A 0 2 3, A 0 2 4, A 0 2 5, A 0 3 4, A 0 3 5, A 0 4 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def constraintMatrixDataRow_1 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![-A 0 0 2, -A 0 0 3, -A 0 0 4, -A 0 0 5, 0, 0, 0, 0, 0, 0, A 0 2 3, A 0 2 4, A 0 2 5, A 0 3 4, A 0 3 5, A 0 4 5, 0, 0, 0, 0]

private def constraintMatrixDataRow_2 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![A 0 0 1, 0, 0, 0, -A 0 0 3, -A 0 0 4, -A 0 0 5, 0, 0, 0, -A 0 1 3, -A 0 1 4, -A 0 1 5, 0, 0, 0, A 0 3 4, A 0 3 5, A 0 4 5, 0]

private def constraintMatrixDataRow_3 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![0, A 0 0 1, 0, 0, A 0 0 2, 0, 0, -A 0 0 4, -A 0 0 5, 0, A 0 1 2, 0, 0, -A 0 1 4, -A 0 1 5, 0, -A 0 2 4, -A 0 2 5, 0, A 0 4 5]

private def constraintMatrixDataRow_4 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![0, 0, A 0 0 1, 0, 0, A 0 0 2, 0, A 0 0 3, 0, -A 0 0 5, 0, A 0 1 2, 0, A 0 1 3, 0, -A 0 1 5, A 0 2 3, 0, -A 0 2 5, -A 0 3 5]

private def constraintMatrixDataRow_5 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![0, 0, 0, A 0 0 1, 0, 0, A 0 0 2, 0, A 0 0 3, A 0 0 4, 0, 0, A 0 1 2, 0, A 0 1 3, A 0 1 4, 0, A 0 2 3, A 0 2 4, A 0 3 4]

private def constraintMatrixDataRow_6 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![A 1 1 2, A 1 1 3, A 1 1 4, A 1 1 5, A 1 2 3, A 1 2 4, A 1 2 5, A 1 3 4, A 1 3 5, A 1 4 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def constraintMatrixDataRow_7 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![-A 1 0 2, -A 1 0 3, -A 1 0 4, -A 1 0 5, 0, 0, 0, 0, 0, 0, A 1 2 3, A 1 2 4, A 1 2 5, A 1 3 4, A 1 3 5, A 1 4 5, 0, 0, 0, 0]

private def constraintMatrixDataRow_8 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![A 1 0 1, 0, 0, 0, -A 1 0 3, -A 1 0 4, -A 1 0 5, 0, 0, 0, -A 1 1 3, -A 1 1 4, -A 1 1 5, 0, 0, 0, A 1 3 4, A 1 3 5, A 1 4 5, 0]

private def constraintMatrixDataRow_9 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![0, A 1 0 1, 0, 0, A 1 0 2, 0, 0, -A 1 0 4, -A 1 0 5, 0, A 1 1 2, 0, 0, -A 1 1 4, -A 1 1 5, 0, -A 1 2 4, -A 1 2 5, 0, A 1 4 5]

private def constraintMatrixDataRow_10 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![0, 0, A 1 0 1, 0, 0, A 1 0 2, 0, A 1 0 3, 0, -A 1 0 5, 0, A 1 1 2, 0, A 1 1 3, 0, -A 1 1 5, A 1 2 3, 0, -A 1 2 5, -A 1 3 5]

private def constraintMatrixDataRow_11 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![0, 0, 0, A 1 0 1, 0, 0, A 1 0 2, 0, A 1 0 3, A 1 0 4, 0, 0, A 1 1 2, 0, A 1 1 3, A 1 1 4, 0, A 1 2 3, A 1 2 4, A 1 3 4]

private def constraintMatrixDataRow_12 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![A 2 1 2, A 2 1 3, A 2 1 4, A 2 1 5, A 2 2 3, A 2 2 4, A 2 2 5, A 2 3 4, A 2 3 5, A 2 4 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def constraintMatrixDataRow_13 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![-A 2 0 2, -A 2 0 3, -A 2 0 4, -A 2 0 5, 0, 0, 0, 0, 0, 0, A 2 2 3, A 2 2 4, A 2 2 5, A 2 3 4, A 2 3 5, A 2 4 5, 0, 0, 0, 0]

private def constraintMatrixDataRow_14 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![A 2 0 1, 0, 0, 0, -A 2 0 3, -A 2 0 4, -A 2 0 5, 0, 0, 0, -A 2 1 3, -A 2 1 4, -A 2 1 5, 0, 0, 0, A 2 3 4, A 2 3 5, A 2 4 5, 0]

private def constraintMatrixDataRow_15 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![0, A 2 0 1, 0, 0, A 2 0 2, 0, 0, -A 2 0 4, -A 2 0 5, 0, A 2 1 2, 0, 0, -A 2 1 4, -A 2 1 5, 0, -A 2 2 4, -A 2 2 5, 0, A 2 4 5]

private def constraintMatrixDataRow_16 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![0, 0, A 2 0 1, 0, 0, A 2 0 2, 0, A 2 0 3, 0, -A 2 0 5, 0, A 2 1 2, 0, A 2 1 3, 0, -A 2 1 5, A 2 2 3, 0, -A 2 2 5, -A 2 3 5]

private def constraintMatrixDataRow_17 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![0, 0, 0, A 2 0 1, 0, 0, A 2 0 2, 0, A 2 0 3, A 2 0 4, 0, 0, A 2 1 2, 0, A 2 1 3, A 2 1 4, 0, A 2 2 3, A 2 2 4, A 2 3 4]

private def constraintMatrixDataRow_18 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

private def constraintMatrixDataRow_19 (A : Fin 3 → Mat R 6) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]

def constraintMatrix (A : Fin 3 → Mat R 6) : Mat R 20 := fun i =>
  match i.val with
  | 0 => constraintMatrixDataRow_0 A
  | 1 => constraintMatrixDataRow_1 A
  | 2 => constraintMatrixDataRow_2 A
  | 3 => constraintMatrixDataRow_3 A
  | 4 => constraintMatrixDataRow_4 A
  | 5 => constraintMatrixDataRow_5 A
  | 6 => constraintMatrixDataRow_6 A
  | 7 => constraintMatrixDataRow_7 A
  | 8 => constraintMatrixDataRow_8 A
  | 9 => constraintMatrixDataRow_9 A
  | 10 => constraintMatrixDataRow_10 A
  | 11 => constraintMatrixDataRow_11 A
  | 12 => constraintMatrixDataRow_12 A
  | 13 => constraintMatrixDataRow_13 A
  | 14 => constraintMatrixDataRow_14 A
  | 15 => constraintMatrixDataRow_15 A
  | 16 => constraintMatrixDataRow_16 A
  | 17 => constraintMatrixDataRow_17 A
  | 18 => constraintMatrixDataRow_18 A
  | 19 => constraintMatrixDataRow_19 A
  | _ => 0

theorem constraintMatrix_row_0 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 0 = contract3 (A 0) p 0 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (A 0 1 2) * p 0 + ((A 0 1 3) * p 1 + ((A 0 1 4) * p 2 + ((A 0 1 5) * p 3 + ((A 0 2 3) * p 4 + ((A 0 2 4) * p 5 + ((A 0 2 5) * p 6 + ((A 0 3 4) * p 7 + ((A 0 3 5) * p 8 + ((A 0 4 5) * p 9 + ((0) * p 10 + ((0) * p 11 + ((0) * p 12 + ((0) * p 13 + ((0) * p 14 + ((0) * p 15 + ((0) * p 16 + ((0) * p 17 + ((0) * p 18 + ((0) * p 19))))))))))))))))))) = p 0 * A 0 1 2 + p 1 * A 0 1 3 + p 2 * A 0 1 4 + p 3 * A 0 1 5 + p 4 * A 0 2 3 + p 5 * A 0 2 4 + p 6 * A 0 2 5 + p 7 * A 0 3 4 + p 8 * A 0 3 5 + p 9 * A 0 4 5
  ring

theorem constraintMatrix_row_1 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 1 = contract3 (A 0) p 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-A 0 0 2) * p 0 + ((-A 0 0 3) * p 1 + ((-A 0 0 4) * p 2 + ((-A 0 0 5) * p 3 + ((0) * p 4 + ((0) * p 5 + ((0) * p 6 + ((0) * p 7 + ((0) * p 8 + ((0) * p 9 + ((A 0 2 3) * p 10 + ((A 0 2 4) * p 11 + ((A 0 2 5) * p 12 + ((A 0 3 4) * p 13 + ((A 0 3 5) * p 14 + ((A 0 4 5) * p 15 + ((0) * p 16 + ((0) * p 17 + ((0) * p 18 + ((0) * p 19))))))))))))))))))) = - p 0 * A 0 0 2 - p 1 * A 0 0 3 - p 2 * A 0 0 4 - p 3 * A 0 0 5 + p 10 * A 0 2 3 + p 11 * A 0 2 4 + p 12 * A 0 2 5 + p 13 * A 0 3 4 + p 14 * A 0 3 5 + p 15 * A 0 4 5
  ring

theorem constraintMatrix_row_2 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 2 = contract3 (A 0) p 2 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (A 0 0 1) * p 0 + ((0) * p 1 + ((0) * p 2 + ((0) * p 3 + ((-A 0 0 3) * p 4 + ((-A 0 0 4) * p 5 + ((-A 0 0 5) * p 6 + ((0) * p 7 + ((0) * p 8 + ((0) * p 9 + ((-A 0 1 3) * p 10 + ((-A 0 1 4) * p 11 + ((-A 0 1 5) * p 12 + ((0) * p 13 + ((0) * p 14 + ((0) * p 15 + ((A 0 3 4) * p 16 + ((A 0 3 5) * p 17 + ((A 0 4 5) * p 18 + ((0) * p 19))))))))))))))))))) = p 0 * A 0 0 1 - p 4 * A 0 0 3 - p 5 * A 0 0 4 - p 6 * A 0 0 5 - p 10 * A 0 1 3 - p 11 * A 0 1 4 - p 12 * A 0 1 5 + p 16 * A 0 3 4 + p 17 * A 0 3 5 + p 18 * A 0 4 5
  ring

theorem constraintMatrix_row_3 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 3 = contract3 (A 0) p 3 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * p 0 + ((A 0 0 1) * p 1 + ((0) * p 2 + ((0) * p 3 + ((A 0 0 2) * p 4 + ((0) * p 5 + ((0) * p 6 + ((-A 0 0 4) * p 7 + ((-A 0 0 5) * p 8 + ((0) * p 9 + ((A 0 1 2) * p 10 + ((0) * p 11 + ((0) * p 12 + ((-A 0 1 4) * p 13 + ((-A 0 1 5) * p 14 + ((0) * p 15 + ((-A 0 2 4) * p 16 + ((-A 0 2 5) * p 17 + ((0) * p 18 + ((A 0 4 5) * p 19))))))))))))))))))) = p 1 * A 0 0 1 + p 4 * A 0 0 2 - p 7 * A 0 0 4 - p 8 * A 0 0 5 + p 10 * A 0 1 2 - p 13 * A 0 1 4 - p 14 * A 0 1 5 - p 16 * A 0 2 4 - p 17 * A 0 2 5 + p 19 * A 0 4 5
  ring

theorem constraintMatrix_row_4 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 4 = contract3 (A 0) p 4 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * p 0 + ((0) * p 1 + ((A 0 0 1) * p 2 + ((0) * p 3 + ((0) * p 4 + ((A 0 0 2) * p 5 + ((0) * p 6 + ((A 0 0 3) * p 7 + ((0) * p 8 + ((-A 0 0 5) * p 9 + ((0) * p 10 + ((A 0 1 2) * p 11 + ((0) * p 12 + ((A 0 1 3) * p 13 + ((0) * p 14 + ((-A 0 1 5) * p 15 + ((A 0 2 3) * p 16 + ((0) * p 17 + ((-A 0 2 5) * p 18 + ((-A 0 3 5) * p 19))))))))))))))))))) = p 2 * A 0 0 1 + p 5 * A 0 0 2 + p 7 * A 0 0 3 - p 9 * A 0 0 5 + p 11 * A 0 1 2 + p 13 * A 0 1 3 - p 15 * A 0 1 5 + p 16 * A 0 2 3 - p 18 * A 0 2 5 - p 19 * A 0 3 5
  ring

theorem constraintMatrix_row_5 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 5 = contract3 (A 0) p 5 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * p 0 + ((0) * p 1 + ((0) * p 2 + ((A 0 0 1) * p 3 + ((0) * p 4 + ((0) * p 5 + ((A 0 0 2) * p 6 + ((0) * p 7 + ((A 0 0 3) * p 8 + ((A 0 0 4) * p 9 + ((0) * p 10 + ((0) * p 11 + ((A 0 1 2) * p 12 + ((0) * p 13 + ((A 0 1 3) * p 14 + ((A 0 1 4) * p 15 + ((0) * p 16 + ((A 0 2 3) * p 17 + ((A 0 2 4) * p 18 + ((A 0 3 4) * p 19))))))))))))))))))) = p 3 * A 0 0 1 + p 6 * A 0 0 2 + p 8 * A 0 0 3 + p 9 * A 0 0 4 + p 12 * A 0 1 2 + p 14 * A 0 1 3 + p 15 * A 0 1 4 + p 17 * A 0 2 3 + p 18 * A 0 2 4 + p 19 * A 0 3 4
  ring

theorem constraintMatrix_row_6 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 6 = contract3 (A 1) p 0 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (A 1 1 2) * p 0 + ((A 1 1 3) * p 1 + ((A 1 1 4) * p 2 + ((A 1 1 5) * p 3 + ((A 1 2 3) * p 4 + ((A 1 2 4) * p 5 + ((A 1 2 5) * p 6 + ((A 1 3 4) * p 7 + ((A 1 3 5) * p 8 + ((A 1 4 5) * p 9 + ((0) * p 10 + ((0) * p 11 + ((0) * p 12 + ((0) * p 13 + ((0) * p 14 + ((0) * p 15 + ((0) * p 16 + ((0) * p 17 + ((0) * p 18 + ((0) * p 19))))))))))))))))))) = p 0 * A 1 1 2 + p 1 * A 1 1 3 + p 2 * A 1 1 4 + p 3 * A 1 1 5 + p 4 * A 1 2 3 + p 5 * A 1 2 4 + p 6 * A 1 2 5 + p 7 * A 1 3 4 + p 8 * A 1 3 5 + p 9 * A 1 4 5
  ring

theorem constraintMatrix_row_7 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 7 = contract3 (A 1) p 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-A 1 0 2) * p 0 + ((-A 1 0 3) * p 1 + ((-A 1 0 4) * p 2 + ((-A 1 0 5) * p 3 + ((0) * p 4 + ((0) * p 5 + ((0) * p 6 + ((0) * p 7 + ((0) * p 8 + ((0) * p 9 + ((A 1 2 3) * p 10 + ((A 1 2 4) * p 11 + ((A 1 2 5) * p 12 + ((A 1 3 4) * p 13 + ((A 1 3 5) * p 14 + ((A 1 4 5) * p 15 + ((0) * p 16 + ((0) * p 17 + ((0) * p 18 + ((0) * p 19))))))))))))))))))) = - p 0 * A 1 0 2 - p 1 * A 1 0 3 - p 2 * A 1 0 4 - p 3 * A 1 0 5 + p 10 * A 1 2 3 + p 11 * A 1 2 4 + p 12 * A 1 2 5 + p 13 * A 1 3 4 + p 14 * A 1 3 5 + p 15 * A 1 4 5
  ring

theorem constraintMatrix_row_8 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 8 = contract3 (A 1) p 2 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (A 1 0 1) * p 0 + ((0) * p 1 + ((0) * p 2 + ((0) * p 3 + ((-A 1 0 3) * p 4 + ((-A 1 0 4) * p 5 + ((-A 1 0 5) * p 6 + ((0) * p 7 + ((0) * p 8 + ((0) * p 9 + ((-A 1 1 3) * p 10 + ((-A 1 1 4) * p 11 + ((-A 1 1 5) * p 12 + ((0) * p 13 + ((0) * p 14 + ((0) * p 15 + ((A 1 3 4) * p 16 + ((A 1 3 5) * p 17 + ((A 1 4 5) * p 18 + ((0) * p 19))))))))))))))))))) = p 0 * A 1 0 1 - p 4 * A 1 0 3 - p 5 * A 1 0 4 - p 6 * A 1 0 5 - p 10 * A 1 1 3 - p 11 * A 1 1 4 - p 12 * A 1 1 5 + p 16 * A 1 3 4 + p 17 * A 1 3 5 + p 18 * A 1 4 5
  ring

theorem constraintMatrix_row_9 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 9 = contract3 (A 1) p 3 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * p 0 + ((A 1 0 1) * p 1 + ((0) * p 2 + ((0) * p 3 + ((A 1 0 2) * p 4 + ((0) * p 5 + ((0) * p 6 + ((-A 1 0 4) * p 7 + ((-A 1 0 5) * p 8 + ((0) * p 9 + ((A 1 1 2) * p 10 + ((0) * p 11 + ((0) * p 12 + ((-A 1 1 4) * p 13 + ((-A 1 1 5) * p 14 + ((0) * p 15 + ((-A 1 2 4) * p 16 + ((-A 1 2 5) * p 17 + ((0) * p 18 + ((A 1 4 5) * p 19))))))))))))))))))) = p 1 * A 1 0 1 + p 4 * A 1 0 2 - p 7 * A 1 0 4 - p 8 * A 1 0 5 + p 10 * A 1 1 2 - p 13 * A 1 1 4 - p 14 * A 1 1 5 - p 16 * A 1 2 4 - p 17 * A 1 2 5 + p 19 * A 1 4 5
  ring

theorem constraintMatrix_row_10 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 10 = contract3 (A 1) p 4 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * p 0 + ((0) * p 1 + ((A 1 0 1) * p 2 + ((0) * p 3 + ((0) * p 4 + ((A 1 0 2) * p 5 + ((0) * p 6 + ((A 1 0 3) * p 7 + ((0) * p 8 + ((-A 1 0 5) * p 9 + ((0) * p 10 + ((A 1 1 2) * p 11 + ((0) * p 12 + ((A 1 1 3) * p 13 + ((0) * p 14 + ((-A 1 1 5) * p 15 + ((A 1 2 3) * p 16 + ((0) * p 17 + ((-A 1 2 5) * p 18 + ((-A 1 3 5) * p 19))))))))))))))))))) = p 2 * A 1 0 1 + p 5 * A 1 0 2 + p 7 * A 1 0 3 - p 9 * A 1 0 5 + p 11 * A 1 1 2 + p 13 * A 1 1 3 - p 15 * A 1 1 5 + p 16 * A 1 2 3 - p 18 * A 1 2 5 - p 19 * A 1 3 5
  ring

theorem constraintMatrix_row_11 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 11 = contract3 (A 1) p 5 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * p 0 + ((0) * p 1 + ((0) * p 2 + ((A 1 0 1) * p 3 + ((0) * p 4 + ((0) * p 5 + ((A 1 0 2) * p 6 + ((0) * p 7 + ((A 1 0 3) * p 8 + ((A 1 0 4) * p 9 + ((0) * p 10 + ((0) * p 11 + ((A 1 1 2) * p 12 + ((0) * p 13 + ((A 1 1 3) * p 14 + ((A 1 1 4) * p 15 + ((0) * p 16 + ((A 1 2 3) * p 17 + ((A 1 2 4) * p 18 + ((A 1 3 4) * p 19))))))))))))))))))) = p 3 * A 1 0 1 + p 6 * A 1 0 2 + p 8 * A 1 0 3 + p 9 * A 1 0 4 + p 12 * A 1 1 2 + p 14 * A 1 1 3 + p 15 * A 1 1 4 + p 17 * A 1 2 3 + p 18 * A 1 2 4 + p 19 * A 1 3 4
  ring

theorem constraintMatrix_row_12 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 12 = contract3 (A 2) p 0 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (A 2 1 2) * p 0 + ((A 2 1 3) * p 1 + ((A 2 1 4) * p 2 + ((A 2 1 5) * p 3 + ((A 2 2 3) * p 4 + ((A 2 2 4) * p 5 + ((A 2 2 5) * p 6 + ((A 2 3 4) * p 7 + ((A 2 3 5) * p 8 + ((A 2 4 5) * p 9 + ((0) * p 10 + ((0) * p 11 + ((0) * p 12 + ((0) * p 13 + ((0) * p 14 + ((0) * p 15 + ((0) * p 16 + ((0) * p 17 + ((0) * p 18 + ((0) * p 19))))))))))))))))))) = p 0 * A 2 1 2 + p 1 * A 2 1 3 + p 2 * A 2 1 4 + p 3 * A 2 1 5 + p 4 * A 2 2 3 + p 5 * A 2 2 4 + p 6 * A 2 2 5 + p 7 * A 2 3 4 + p 8 * A 2 3 5 + p 9 * A 2 4 5
  ring

theorem constraintMatrix_row_13 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 13 = contract3 (A 2) p 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-A 2 0 2) * p 0 + ((-A 2 0 3) * p 1 + ((-A 2 0 4) * p 2 + ((-A 2 0 5) * p 3 + ((0) * p 4 + ((0) * p 5 + ((0) * p 6 + ((0) * p 7 + ((0) * p 8 + ((0) * p 9 + ((A 2 2 3) * p 10 + ((A 2 2 4) * p 11 + ((A 2 2 5) * p 12 + ((A 2 3 4) * p 13 + ((A 2 3 5) * p 14 + ((A 2 4 5) * p 15 + ((0) * p 16 + ((0) * p 17 + ((0) * p 18 + ((0) * p 19))))))))))))))))))) = - p 0 * A 2 0 2 - p 1 * A 2 0 3 - p 2 * A 2 0 4 - p 3 * A 2 0 5 + p 10 * A 2 2 3 + p 11 * A 2 2 4 + p 12 * A 2 2 5 + p 13 * A 2 3 4 + p 14 * A 2 3 5 + p 15 * A 2 4 5
  ring

theorem constraintMatrix_row_14 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 14 = contract3 (A 2) p 2 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (A 2 0 1) * p 0 + ((0) * p 1 + ((0) * p 2 + ((0) * p 3 + ((-A 2 0 3) * p 4 + ((-A 2 0 4) * p 5 + ((-A 2 0 5) * p 6 + ((0) * p 7 + ((0) * p 8 + ((0) * p 9 + ((-A 2 1 3) * p 10 + ((-A 2 1 4) * p 11 + ((-A 2 1 5) * p 12 + ((0) * p 13 + ((0) * p 14 + ((0) * p 15 + ((A 2 3 4) * p 16 + ((A 2 3 5) * p 17 + ((A 2 4 5) * p 18 + ((0) * p 19))))))))))))))))))) = p 0 * A 2 0 1 - p 4 * A 2 0 3 - p 5 * A 2 0 4 - p 6 * A 2 0 5 - p 10 * A 2 1 3 - p 11 * A 2 1 4 - p 12 * A 2 1 5 + p 16 * A 2 3 4 + p 17 * A 2 3 5 + p 18 * A 2 4 5
  ring

theorem constraintMatrix_row_15 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 15 = contract3 (A 2) p 3 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * p 0 + ((A 2 0 1) * p 1 + ((0) * p 2 + ((0) * p 3 + ((A 2 0 2) * p 4 + ((0) * p 5 + ((0) * p 6 + ((-A 2 0 4) * p 7 + ((-A 2 0 5) * p 8 + ((0) * p 9 + ((A 2 1 2) * p 10 + ((0) * p 11 + ((0) * p 12 + ((-A 2 1 4) * p 13 + ((-A 2 1 5) * p 14 + ((0) * p 15 + ((-A 2 2 4) * p 16 + ((-A 2 2 5) * p 17 + ((0) * p 18 + ((A 2 4 5) * p 19))))))))))))))))))) = p 1 * A 2 0 1 + p 4 * A 2 0 2 - p 7 * A 2 0 4 - p 8 * A 2 0 5 + p 10 * A 2 1 2 - p 13 * A 2 1 4 - p 14 * A 2 1 5 - p 16 * A 2 2 4 - p 17 * A 2 2 5 + p 19 * A 2 4 5
  ring

theorem constraintMatrix_row_16 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 16 = contract3 (A 2) p 4 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * p 0 + ((0) * p 1 + ((A 2 0 1) * p 2 + ((0) * p 3 + ((0) * p 4 + ((A 2 0 2) * p 5 + ((0) * p 6 + ((A 2 0 3) * p 7 + ((0) * p 8 + ((-A 2 0 5) * p 9 + ((0) * p 10 + ((A 2 1 2) * p 11 + ((0) * p 12 + ((A 2 1 3) * p 13 + ((0) * p 14 + ((-A 2 1 5) * p 15 + ((A 2 2 3) * p 16 + ((0) * p 17 + ((-A 2 2 5) * p 18 + ((-A 2 3 5) * p 19))))))))))))))))))) = p 2 * A 2 0 1 + p 5 * A 2 0 2 + p 7 * A 2 0 3 - p 9 * A 2 0 5 + p 11 * A 2 1 2 + p 13 * A 2 1 3 - p 15 * A 2 1 5 + p 16 * A 2 2 3 - p 18 * A 2 2 5 - p 19 * A 2 3 5
  ring

theorem constraintMatrix_row_17 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 17 = contract3 (A 2) p 5 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * p 0 + ((0) * p 1 + ((0) * p 2 + ((A 2 0 1) * p 3 + ((0) * p 4 + ((0) * p 5 + ((A 2 0 2) * p 6 + ((0) * p 7 + ((A 2 0 3) * p 8 + ((A 2 0 4) * p 9 + ((0) * p 10 + ((0) * p 11 + ((A 2 1 2) * p 12 + ((0) * p 13 + ((A 2 1 3) * p 14 + ((A 2 1 4) * p 15 + ((0) * p 16 + ((A 2 2 3) * p 17 + ((A 2 2 4) * p 18 + ((A 2 3 4) * p 19))))))))))))))))))) = p 3 * A 2 0 1 + p 6 * A 2 0 2 + p 8 * A 2 0 3 + p 9 * A 2 0 4 + p 12 * A 2 1 2 + p 14 * A 2 1 3 + p 15 * A 2 1 4 + p 17 * A 2 2 3 + p 18 * A 2 2 4 + p 19 * A 2 3 4
  ring

theorem constraintMatrix_row_18 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 18 = p 13 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * p 0 + ((0) * p 1 + ((0) * p 2 + ((0) * p 3 + ((0) * p 4 + ((0) * p 5 + ((0) * p 6 + ((0) * p 7 + ((0) * p 8 + ((0) * p 9 + ((0) * p 10 + ((0) * p 11 + ((0) * p 12 + ((1) * p 13 + ((0) * p 14 + ((0) * p 15 + ((0) * p 16 + ((0) * p 17 + ((0) * p 18 + ((0) * p 19))))))))))))))))))) = p 13
  ring

theorem constraintMatrix_row_19 (A : Fin 3 → Mat R 6) (p : Vec R 20) :
    (constraintMatrix A).mulVec p 19 = p 14 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * p 0 + ((0) * p 1 + ((0) * p 2 + ((0) * p 3 + ((0) * p 4 + ((0) * p 5 + ((0) * p 6 + ((0) * p 7 + ((0) * p 8 + ((0) * p 9 + ((0) * p 10 + ((0) * p 11 + ((0) * p 12 + ((0) * p 13 + ((1) * p 14 + ((0) * p 15 + ((0) * p 16 + ((0) * p 17 + ((0) * p 18 + ((0) * p 19))))))))))))))))))) = p 14
  ring

variable {S : Type*} [CommRing S]

private theorem constraintMatrix_map_row_0 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 0 = constraintMatrix (fun j => (A j).map f) 0 := by
  funext j
  fin_cases j
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem constraintMatrix_map_row_1 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 1 = constraintMatrix (fun j => (A j).map f) 1 := by
  funext j
  fin_cases j
  · exact map_neg f (A 0 0 2)
  · exact map_neg f (A 0 0 3)
  · exact map_neg f (A 0 0 4)
  · exact map_neg f (A 0 0 5)
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem constraintMatrix_map_row_2 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 2 = constraintMatrix (fun j => (A j).map f) 2 := by
  funext j
  fin_cases j
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_neg f (A 0 0 3)
  · exact map_neg f (A 0 0 4)
  · exact map_neg f (A 0 0 5)
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_neg f (A 0 1 3)
  · exact map_neg f (A 0 1 4)
  · exact map_neg f (A 0 1 5)
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · rfl
  · rfl
  · exact map_zero f

private theorem constraintMatrix_map_row_3 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 3 = constraintMatrix (fun j => (A j).map f) 3 := by
  funext j
  fin_cases j
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_neg f (A 0 0 4)
  · exact map_neg f (A 0 0 5)
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_neg f (A 0 1 4)
  · exact map_neg f (A 0 1 5)
  · exact map_zero f
  · exact map_neg f (A 0 2 4)
  · exact map_neg f (A 0 2 5)
  · exact map_zero f
  · rfl

private theorem constraintMatrix_map_row_4 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 4 = constraintMatrix (fun j => (A j).map f) 4 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_neg f (A 0 0 5)
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_neg f (A 0 1 5)
  · rfl
  · exact map_zero f
  · exact map_neg f (A 0 2 5)
  · exact map_neg f (A 0 3 5)

private theorem constraintMatrix_map_row_5 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 5 = constraintMatrix (fun j => (A j).map f) 5 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · rfl
  · rfl
  · rfl

private theorem constraintMatrix_map_row_6 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 6 = constraintMatrix (fun j => (A j).map f) 6 := by
  funext j
  fin_cases j
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem constraintMatrix_map_row_7 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 7 = constraintMatrix (fun j => (A j).map f) 7 := by
  funext j
  fin_cases j
  · exact map_neg f (A 1 0 2)
  · exact map_neg f (A 1 0 3)
  · exact map_neg f (A 1 0 4)
  · exact map_neg f (A 1 0 5)
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem constraintMatrix_map_row_8 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 8 = constraintMatrix (fun j => (A j).map f) 8 := by
  funext j
  fin_cases j
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_neg f (A 1 0 3)
  · exact map_neg f (A 1 0 4)
  · exact map_neg f (A 1 0 5)
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_neg f (A 1 1 3)
  · exact map_neg f (A 1 1 4)
  · exact map_neg f (A 1 1 5)
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · rfl
  · rfl
  · exact map_zero f

private theorem constraintMatrix_map_row_9 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 9 = constraintMatrix (fun j => (A j).map f) 9 := by
  funext j
  fin_cases j
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_neg f (A 1 0 4)
  · exact map_neg f (A 1 0 5)
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_neg f (A 1 1 4)
  · exact map_neg f (A 1 1 5)
  · exact map_zero f
  · exact map_neg f (A 1 2 4)
  · exact map_neg f (A 1 2 5)
  · exact map_zero f
  · rfl

private theorem constraintMatrix_map_row_10 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 10 = constraintMatrix (fun j => (A j).map f) 10 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_neg f (A 1 0 5)
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_neg f (A 1 1 5)
  · rfl
  · exact map_zero f
  · exact map_neg f (A 1 2 5)
  · exact map_neg f (A 1 3 5)

private theorem constraintMatrix_map_row_11 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 11 = constraintMatrix (fun j => (A j).map f) 11 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · rfl
  · rfl
  · rfl

private theorem constraintMatrix_map_row_12 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 12 = constraintMatrix (fun j => (A j).map f) 12 := by
  funext j
  fin_cases j
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem constraintMatrix_map_row_13 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 13 = constraintMatrix (fun j => (A j).map f) 13 := by
  funext j
  fin_cases j
  · exact map_neg f (A 2 0 2)
  · exact map_neg f (A 2 0 3)
  · exact map_neg f (A 2 0 4)
  · exact map_neg f (A 2 0 5)
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem constraintMatrix_map_row_14 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 14 = constraintMatrix (fun j => (A j).map f) 14 := by
  funext j
  fin_cases j
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_neg f (A 2 0 3)
  · exact map_neg f (A 2 0 4)
  · exact map_neg f (A 2 0 5)
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_neg f (A 2 1 3)
  · exact map_neg f (A 2 1 4)
  · exact map_neg f (A 2 1 5)
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · rfl
  · rfl
  · exact map_zero f

private theorem constraintMatrix_map_row_15 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 15 = constraintMatrix (fun j => (A j).map f) 15 := by
  funext j
  fin_cases j
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_neg f (A 2 0 4)
  · exact map_neg f (A 2 0 5)
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_neg f (A 2 1 4)
  · exact map_neg f (A 2 1 5)
  · exact map_zero f
  · exact map_neg f (A 2 2 4)
  · exact map_neg f (A 2 2 5)
  · exact map_zero f
  · rfl

private theorem constraintMatrix_map_row_16 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 16 = constraintMatrix (fun j => (A j).map f) 16 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_neg f (A 2 0 5)
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_neg f (A 2 1 5)
  · rfl
  · exact map_zero f
  · exact map_neg f (A 2 2 5)
  · exact map_neg f (A 2 3 5)

private theorem constraintMatrix_map_row_17 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 17 = constraintMatrix (fun j => (A j).map f) 17 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · rfl
  · rfl
  · rfl

private theorem constraintMatrix_map_row_18 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 18 = constraintMatrix (fun j => (A j).map f) 18 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem constraintMatrix_map_row_19 (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f 19 = constraintMatrix (fun j => (A j).map f) 19 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

theorem constraintMatrix_map (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).map f = constraintMatrix (fun j => (A j).map f) := by
  funext i
  fin_cases i
  · exact constraintMatrix_map_row_0 f A
  · exact constraintMatrix_map_row_1 f A
  · exact constraintMatrix_map_row_2 f A
  · exact constraintMatrix_map_row_3 f A
  · exact constraintMatrix_map_row_4 f A
  · exact constraintMatrix_map_row_5 f A
  · exact constraintMatrix_map_row_6 f A
  · exact constraintMatrix_map_row_7 f A
  · exact constraintMatrix_map_row_8 f A
  · exact constraintMatrix_map_row_9 f A
  · exact constraintMatrix_map_row_10 f A
  · exact constraintMatrix_map_row_11 f A
  · exact constraintMatrix_map_row_12 f A
  · exact constraintMatrix_map_row_13 f A
  · exact constraintMatrix_map_row_14 f A
  · exact constraintMatrix_map_row_15 f A
  · exact constraintMatrix_map_row_16 f A
  · exact constraintMatrix_map_row_17 f A
  · exact constraintMatrix_map_row_18 f A
  · exact constraintMatrix_map_row_19 f A

/-- The concrete triple from Section 2 of the source note. -/
def goodTriple : Fin 3 → Mat R 6 :=
  ![!![0, 1, 0, 0, 0, 0; -1, 0, 0, 0, 0, 0; 0, 0, 0, 1, 0, 0; 0, 0, -1, 0, 0, 0; 0, 0, 0, 0, 0, 1; 0, 0, 0, 0, -1, 0],
    !![0, 1, 0, 0, 0, 0; -1, 0, 0, 0, 0, 0; 0, 0, 0, 2, 0, 0; 0, 0, -2, 0, 0, 0; 0, 0, 0, 0, 0, 3; 0, 0, 0, 0, -3, 0],
    !![0, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1; -1, 0, 0, 0, 1, 0; 0, -1, 0, 0, 0, 2; -1, 0, -1, 0, 0, 0; 0, -1, 0, -2, 0, 0]]

/-- A rational stable three-vector in the contraction kernel of the good triple. -/
def goodTrivector : Vec R 20 := ![0, 0, 0, 0, 0, 2, 0, 0, -1, 0, 0, 0, -2, -2, 0, 0, 0, 0, 0, 0]

theorem goodTrivector_discriminant : trivectorDiscriminant (goodTrivector : Vec R 20) = -32 := by
  change ((0) * (0) - (0) * (0) + (0) * (0) - (0) * (0) + (0) * (0) - (2) * (0) + (0) * (-2) + (0) * (-2) - (-1) * (0) + (0) * (0)) * ((0) * (0) - (0) * (0) + (0) * (0) - (0) * (0) + (0) * (0) - (2) * (0) + (0) * (-2) + (0) * (-2) - (-1) * (0) + (0) * (0)) + ((2 * (0) * (0) - 2 * (0) * (0) + 2 * (-2) * (-2)) * (- 2 * (0) * (0) + 2 * (2) * (-1) - 2 * (0) * (0)) + ((2 * (0) * (0) - 2 * (0) * (0) + 2 * (-2) * (0)) * (2 * (0) * (0) - 2 * (0) * (-1) + 2 * (0) * (0)) + ((2 * (0) * (0) - 2 * (-2) * (0) + 2 * (0) * (0)) * (- 2 * (0) * (0) + 2 * (0) * (0) - 2 * (0) * (2)) + ((2 * (0) * (0) - 2 * (-2) * (0) + 2 * (0) * (0)) * (2 * (0) * (-1) - 2 * (0) * (0) + 2 * (0) * (0)) + ((2 * (-2) * (0) - 2 * (0) * (0) + 2 * (0) * (0)) * (- 2 * (0) * (0) + 2 * (0) * (2) - 2 * (0) * (0))))))) = -32
  norm_num

end Ring

section Field
variable {K : Type*} [Field K] [NeZero (2 : K)]

private theorem goodConstraint_four_ne_zero : (4 : K) ≠ 0 := by
  rw [show (4 : K) = (2 : K) ^ 2 by norm_num]
  exact pow_ne_zero _ (NeZero.ne _)

/-- An exact inverse for the good constraint matrix. -/
private def goodConstraintInverseDataRow_0  : Vec K 20 :=
  ![0, 0, (3 / 2), 0, 0, 0, 0, 0, (-1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def goodConstraintInverseDataRow_1  : Vec K 20 :=
  ![0, 0, 0, (3 / 2), 0, 0, 0, 0, 0, (-1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def goodConstraintInverseDataRow_2  : Vec K 20 :=
  ![0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def goodConstraintInverseDataRow_3  : Vec K 20 :=
  ![0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0]

private def goodConstraintInverseDataRow_4  : Vec K 20 :=
  ![3, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def goodConstraintInverseDataRow_5  : Vec K 20 :=
  ![0, -2, 0, -1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, -1, 0]

private def goodConstraintInverseDataRow_6  : Vec K 20 :=
  ![2, 0, (1 / 2), 0, 0, 0, -1, 0, (-1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, -1]

private def goodConstraintInverseDataRow_7  : Vec K 20 :=
  ![3, 0, 0, 0, 1, 0, -1, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, -1]

private def goodConstraintInverseDataRow_8  : Vec K 20 :=
  ![0, 1, 0, (-1 / 4), 0, -1, 0, (-1 / 2), 0, (-1 / 4), 0, (1 / 2), (1 / 2), 0, 0, 0, (-1 / 2), 0, (1 / 2), 0]

private def goodConstraintInverseDataRow_9  : Vec K 20 :=
  ![-2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def goodConstraintInverseDataRow_10  : Vec K 20 :=
  ![0, 3, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def goodConstraintInverseDataRow_11  : Vec K 20 :=
  ![0, 0, (3 / 2), 0, 2, 0, 0, 0, (-1 / 2), 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -2]

private def goodConstraintInverseDataRow_12  : Vec K 20 :=
  ![0, -1, 0, 1, 0, -2, 0, 0, 0, -1, 0, 2, 0, 0, -1, 0, -1, 0, 1, 0]

private def goodConstraintInverseDataRow_13  : Vec K 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]

private def goodConstraintInverseDataRow_14  : Vec K 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

private def goodConstraintInverseDataRow_15  : Vec K 20 :=
  ![0, -2, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def goodConstraintInverseDataRow_16  : Vec K 20 :=
  ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def goodConstraintInverseDataRow_17  : Vec K 20 :=
  ![0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]

private def goodConstraintInverseDataRow_18  : Vec K 20 :=
  ![0, 0, (-1 / 2), 0, 0, 0, 0, 0, (1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def goodConstraintInverseDataRow_19  : Vec K 20 :=
  ![0, 0, 0, (-1 / 2), 0, 0, 0, 0, 0, (1 / 2), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def goodConstraintInverse  : Mat K 20 := fun i =>
  match i.val with
  | 0 => goodConstraintInverseDataRow_0
  | 1 => goodConstraintInverseDataRow_1
  | 2 => goodConstraintInverseDataRow_2
  | 3 => goodConstraintInverseDataRow_3
  | 4 => goodConstraintInverseDataRow_4
  | 5 => goodConstraintInverseDataRow_5
  | 6 => goodConstraintInverseDataRow_6
  | 7 => goodConstraintInverseDataRow_7
  | 8 => goodConstraintInverseDataRow_8
  | 9 => goodConstraintInverseDataRow_9
  | 10 => goodConstraintInverseDataRow_10
  | 11 => goodConstraintInverseDataRow_11
  | 12 => goodConstraintInverseDataRow_12
  | 13 => goodConstraintInverseDataRow_13
  | 14 => goodConstraintInverseDataRow_14
  | 15 => goodConstraintInverseDataRow_15
  | 16 => goodConstraintInverseDataRow_16
  | 17 => goodConstraintInverseDataRow_17
  | 18 => goodConstraintInverseDataRow_18
  | 19 => goodConstraintInverseDataRow_19
  | _ => 0

private theorem goodConstraintInverse_entry_0_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 0 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (3) + ((0) * (0) + ((0) * (2) + ((0) * (3) + ((0) * (0) + ((1) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_0_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_0_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (2) + ((0) * (3) + ((0) * (0) + ((0) * (-2) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 1 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (3) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_1_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * ((3 / 2)) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * ((3 / 2)) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (2) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * ((-1 / 2)) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * ((-1 / 2)) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_1_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (3) + ((-(0)) * (0) + ((-(0)) * (2) + ((0) * (3) + ((0) * (0) + ((0) * (-2) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-2) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (3) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 2 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((3 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 1
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_2_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (2) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_2_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_2_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-2) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (2) + ((-(0)) * (3) + ((-(0)) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (-2) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * ((-1 / 2)) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 3 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * ((-1 / 2))))))))))))))))))))) : K) = 1
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_3_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 2)) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * ((1 / 2)) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * ((1 / 2))))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_3_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_3_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((1) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (2) + ((0) * (3) + ((0) * (0) + ((-(0)) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (-2) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * ((-1 / 2)) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((3 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 4 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_4_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((-(0)) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (1) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * ((1 / 2)) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((-1 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (1) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_4_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((1) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (2) + ((0) * (3) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (2) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 5 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_5_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_5_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (3) + ((0) * (0) + ((0) * (2) + ((0) * (3) + ((0) * (0) + ((3) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((3) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 6 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (-1) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((3) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_6_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((3) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_6_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (2) + ((0) * (3) + ((0) * (0) + ((0) * (-2) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((2) * (3) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((3) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * ((3 / 2)) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * ((3 / 2)) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (2) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (1) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 7 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((2) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_7_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * ((-1 / 2)) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * ((-1 / 2)) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (1) + ((0) * (0) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_7_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (3) + ((-(0)) * (0) + ((-(0)) * (2) + ((0) * (3) + ((0) * (0) + ((0) * (-2) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-2) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (3) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((3 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_8_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (2) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 8 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 1
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_8_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_8_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-2) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((3) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (2) + ((-(0)) * (3) + ((-(0)) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (-2) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * ((-1 / 2)) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * ((-1 / 2))))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_9_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 2)) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * ((1 / 2)) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 9 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * ((1 / 2))))))))))))))))))))) : K) = 1
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_9_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_9_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((3) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (2) + ((0) * (3) + ((0) * (0) + ((-(0)) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (-2) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * ((-1 / 2)) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((3 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((-(0)) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (1) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * ((1 / 2)) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((-1 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 10 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_10_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (1) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_10_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((2) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(0)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (2) + ((0) * (3) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (2) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (-1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 11 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_11_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_11_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (3) + ((1) * (0) + ((0) * (2) + ((0) * (3) + ((2) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (-2) + ((0) * (0) + ((0) * (0) + ((2) * (1) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * ((3 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (0) + ((2) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_12_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (2) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (-1) + ((0) * (-1) + ((2) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((2) * ((-1 / 2)) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_12_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * ((-1 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((2) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_12_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((2) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_12_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 12 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((2) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_12_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((2) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_12_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_12_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (0) + ((2) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_12_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (-1) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (2) + ((0) * (3) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (3) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((2) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * ((3 / 2)) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * ((3 / 2)) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (2) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (2) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-2) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * ((-1 / 2)) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * ((-1 / 2)) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (2) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 13 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_13_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (1) + ((2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_13_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-2) + ((0) * (0) + ((0) * (0) + ((2) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (3) + ((-(1)) * (0) + ((-(0)) * (2) + ((0) * (3) + ((0) * (0) + ((0) * (-2) + ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (-2) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(1)) * (3) + ((-(0)) * (0) + ((-(1)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * ((3 / 2)) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (2) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (-1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (-1) + ((-(1)) * (0) + ((-(0)) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (1) + ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((-(1)) * (-1) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * ((-1 / 2)) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (-1) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (1) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 14 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_14_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((-(1)) * (1) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_14_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((-(0)) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (-2) + ((-(1)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((2) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (3) + ((0) * (0) + ((0) * (2) + ((-(1)) * (3) + ((-(0)) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-2) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (-2) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (-1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (-1) + ((-(1)) * (-1) + ((-(0)) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * ((-1 / 2)) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (1) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 15 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_15_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (1) + ((-(1)) * (0) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_15_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((-(1)) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((-(0)) * (0) + ((-(1)) * (1) + ((0) * (0) + ((-(1)) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (3) + ((1) * (0) + ((0) * (2) + ((0) * (3) + ((0) * (0) + ((-(0)) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((-(1)) * (-2) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * ((-1 / 2)) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * ((-1 / 2))))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_16_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-1) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((-(0)) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((-(1)) * (1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * ((1 / 2)) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * ((1 / 2))))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_16_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (1) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (1) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 16 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_16_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((-(0)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (1) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_16_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((-(0)) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(0)) * (0) + ((-(2)) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((1) * (2) + ((0) * (3) + ((0) * (0) + ((1) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_17_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (-1) + ((0) * (-1) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  field_simp [goodConstraint_four_ne_zero] <;> ring

private theorem goodConstraintInverse_entry_17_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 17 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_17_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_17_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-1) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (2) + ((0) * (3) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_18_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 18 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_entry_18_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (2) + ((0) * (3) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (3) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((3 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2))))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * ((-1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * ((1 / 2)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 0
  norm_num

private theorem goodConstraintInverse_entry_19_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 19 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-1) + ((0) * (-1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-2) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0)))))))))))))))))))) : K) = 1
  norm_num

private theorem goodConstraintInverse_row_0 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 0 = (1 : Mat K 20) 0 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_0_19 (K := K))

private theorem goodConstraintInverse_row_1 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 1 = (1 : Mat K 20) 1 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_1_19 (K := K))

private theorem goodConstraintInverse_row_2 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 2 = (1 : Mat K 20) 2 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_2_19 (K := K))

private theorem goodConstraintInverse_row_3 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 3 = (1 : Mat K 20) 3 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_3_19 (K := K))

private theorem goodConstraintInverse_row_4 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 4 = (1 : Mat K 20) 4 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_4_19 (K := K))

private theorem goodConstraintInverse_row_5 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 5 = (1 : Mat K 20) 5 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_5_19 (K := K))

private theorem goodConstraintInverse_row_6 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 6 = (1 : Mat K 20) 6 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_6_19 (K := K))

private theorem goodConstraintInverse_row_7 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 7 = (1 : Mat K 20) 7 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_7_19 (K := K))

private theorem goodConstraintInverse_row_8 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 8 = (1 : Mat K 20) 8 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_8_19 (K := K))

private theorem goodConstraintInverse_row_9 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 9 = (1 : Mat K 20) 9 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_9_19 (K := K))

private theorem goodConstraintInverse_row_10 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 10 = (1 : Mat K 20) 10 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_10_19 (K := K))

private theorem goodConstraintInverse_row_11 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 11 = (1 : Mat K 20) 11 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_11_19 (K := K))

private theorem goodConstraintInverse_row_12 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 12 = (1 : Mat K 20) 12 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_12_19 (K := K))

private theorem goodConstraintInverse_row_13 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 13 = (1 : Mat K 20) 13 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_13_19 (K := K))

private theorem goodConstraintInverse_row_14 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 14 = (1 : Mat K 20) 14 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_14_19 (K := K))

private theorem goodConstraintInverse_row_15 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 15 = (1 : Mat K 20) 15 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_15_19 (K := K))

private theorem goodConstraintInverse_row_16 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 16 = (1 : Mat K 20) 16 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_16_19 (K := K))

private theorem goodConstraintInverse_row_17 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 17 = (1 : Mat K 20) 17 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_17_19 (K := K))

private theorem goodConstraintInverse_row_18 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 18 = (1 : Mat K 20) 18 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_18_19 (K := K))

private theorem goodConstraintInverse_row_19 :
    (constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20)) 19 = (1 : Mat K 20) 19 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_0 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_1 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_2 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_3 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_4 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_5 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_6 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_7 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_8 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_9 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_10 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_11 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_12 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_13 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_14 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_15 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_16 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_17 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_18 (K := K))
  · simpa [Matrix.one_apply] using (goodConstraintInverse_entry_19_19 (K := K))

theorem goodConstraintInverse_mul :
    constraintMatrix (goodTriple : Fin 3 → Mat K 6) * (goodConstraintInverse : Mat K 20) = 1 := by
  funext i
  fin_cases i
  · exact goodConstraintInverse_row_0
  · exact goodConstraintInverse_row_1
  · exact goodConstraintInverse_row_2
  · exact goodConstraintInverse_row_3
  · exact goodConstraintInverse_row_4
  · exact goodConstraintInverse_row_5
  · exact goodConstraintInverse_row_6
  · exact goodConstraintInverse_row_7
  · exact goodConstraintInverse_row_8
  · exact goodConstraintInverse_row_9
  · exact goodConstraintInverse_row_10
  · exact goodConstraintInverse_row_11
  · exact goodConstraintInverse_row_12
  · exact goodConstraintInverse_row_13
  · exact goodConstraintInverse_row_14
  · exact goodConstraintInverse_row_15
  · exact goodConstraintInverse_row_16
  · exact goodConstraintInverse_row_17
  · exact goodConstraintInverse_row_18
  · exact goodConstraintInverse_row_19

theorem goodConstraint_det_ne_zero : (constraintMatrix (goodTriple : Fin 3 → Mat K 6)).det ≠ 0 := by
  have h := congrArg Matrix.det (goodConstraintInverse_mul (K := K))
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

end Field
end PfaffianDescent
