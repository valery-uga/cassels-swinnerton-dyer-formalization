import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Literal split matrices from an invertible six-column pivot -/
noncomputable section
namespace PfaffianDescent
universe u
variable {R : Type u} [CommRing R]

abbrev serrePivotEvaluation (P : Matrix (Fin 6) (Fin 6) R)
    (Q : Matrix (Fin 6) (Fin 3) R) := Matrix.fromCols P Q
abbrev serrePivotKernelFrame (P : Matrix (Fin 6) (Fin 6) R)
    (Q : Matrix (Fin 6) (Fin 3) R) := Matrix.fromRows (-(P⁻¹ * Q)) (1 : Matrix (Fin 3) (Fin 3) R)
abbrev serrePivotKernelRetraction := Matrix.fromCols
  (0 : Matrix (Fin 3) (Fin 6) R) (1 : Matrix (Fin 3) (Fin 3) R)
abbrev serrePivotEvaluationSplitting (P : Matrix (Fin 6) (Fin 6) R) :=
  Matrix.fromRows P⁻¹ (0 : Matrix (Fin 3) (Fin 6) R)

/-- The three literal graph columns satisfy all six evaluation equations. -/
theorem serrePivotKernelFrame_vanishes
    (P : Matrix (Fin 6) (Fin 6) R) (Q : Matrix (Fin 6) (Fin 3) R)
    (hP : IsUnit P.det) : serrePivotEvaluation P Q * serrePivotKernelFrame P Q = 0 := by
  rw [Matrix.fromCols_mul_fromRows]
  simp only [Matrix.mul_neg, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv P hP,
    Matrix.one_mul, Matrix.mul_one, neg_add_cancel]

/-- The free-coordinate projection is a literal left inverse of the frame. -/
theorem serrePivotKernelFrame_retracts
    (P : Matrix (Fin 6) (Fin 6) R) (Q : Matrix (Fin 6) (Fin 3) R) :
    serrePivotKernelRetraction (R := R) * serrePivotKernelFrame P Q = 1 := by
  rw [Matrix.fromCols_mul_fromRows]
  simp

/-- Every coordinate splits as its kernel part and its evaluation part. -/
theorem serrePivotKernelFrame_decomposition
    (P : Matrix (Fin 6) (Fin 6) R) (Q : Matrix (Fin 6) (Fin 3) R)
    (hP : IsUnit P.det) :
    serrePivotKernelFrame P Q * serrePivotKernelRetraction (R := R) +
      serrePivotEvaluationSplitting P * serrePivotEvaluation P Q = 1 := by
  rw [Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul_fromCols, Matrix.fromBlocks_add]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.nonsing_inv_mul P hP, zero_add, add_zero, neg_add_cancel, Matrix.fromBlocks_one]

end PfaffianDescent
