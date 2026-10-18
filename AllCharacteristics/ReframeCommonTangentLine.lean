import AllCharacteristics.CommonTangentKernelFrame
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Choose a kernel frame whose first column is a
specified noncubic point of the common tangent line. -/

noncomputable section
namespace PfaffianDescent
universe u

theorem exists_invertible_two_matrix_first_column
    {K : Type u} [Field K] (u : Fin 2 → K) (hu : u ≠ 0) :
    ∃ T : Matrix (Fin 2) (Fin 2) K, IsUnit T.det ∧
      T.mulVec (Pi.single 0 1) = u := by
  classical
  by_cases hu0 : u 0 = 0
  · have hu1 : u 1 ≠ 0 := by
      intro hzero
      apply hu
      funext i
      fin_cases i
      · change u 0 = 0
        exact hu0
      · change u 1 = 0
        exact hzero
    let T : Matrix (Fin 2) (Fin 2) K := ![![u 0, 1], ![u 1, 0]]
    refine ⟨T, ?_, ?_⟩
    · apply isUnit_iff_ne_zero.mpr
      rw [Matrix.det_fin_two]
      change u 0 * 0 - 1 * u 1 ≠ 0
      simpa only [mul_zero, one_mul, zero_sub] using neg_ne_zero.mpr hu1
    · rw [Matrix.mulVec_single_one]
      funext i
      fin_cases i <;> rfl
  · let T : Matrix (Fin 2) (Fin 2) K := ![![u 0, 0], ![u 1, 1]]
    refine ⟨T, ?_, ?_⟩
    · apply isUnit_iff_ne_zero.mpr
      rw [Matrix.det_fin_two]
      change u 0 * 1 - 0 * u 1 ≠ 0
      simpa only [mul_one, zero_mul, sub_zero] using hu0
    · rw [Matrix.mulVec_single_one]
      funext i
      fin_cases i <;> rfl

theorem exists_split_kernel_frame_first_column_nonzero_cubic_value
    {K : Type u} [Field K]
    (R : Matrix (Fin 2) (Fin 4) K)
    (A : Matrix (Fin 4) (Fin 2) K) (B : Matrix (Fin 2) (Fin 4) K)
    (S : Matrix (Fin 4) (Fin 2) K)
    (hBA : B * A = 1) (hRA : R * A = 0) (hRS : R * S = 1)
    (c : Cubic K 4) (u : Fin 2 → K) (hcu : c.eval (A.mulVec u) ≠ 0) :
    ∃ (A' : Matrix (Fin 4) (Fin 2) K) (B' : Matrix (Fin 2) (Fin 4) K),
      B' * A' = 1 ∧ R * A' = 0 ∧
      c.eval (fun i ↦ A' i 0) ≠ 0 := by
  have hu : u ≠ 0 := by
    intro hu
    apply hcu
    rw [hu, Matrix.mulVec_zero, Cubic.eval_zero]
  obtain ⟨T, hT, hTu⟩ := exists_invertible_two_matrix_first_column u hu
  let A' := A * T
  let B' := T⁻¹ * B
  have hBA' : B' * A' = 1 := by
    change (T⁻¹ * B) * (A * T) = 1
    calc
      (T⁻¹ * B) * (A * T) = T⁻¹ * ((B * A) * T) := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBA, Matrix.one_mul, Matrix.nonsing_inv_mul T hT]
  have hRA' : R * A' = 0 := by
    change R * (A * T) = 0
    rw [← Matrix.mul_assoc, hRA, Matrix.zero_mul]
  have hcol : (fun i ↦ A' i 0) = A.mulVec u := by
    have he : A'.mulVec (Pi.single 0 1) = A.mulVec u := by
      change (A * T).mulVec (Pi.single 0 1) = A.mulVec u
      rw [← Matrix.mulVec_mulVec, hTu]
    rw [Matrix.mulVec_single_one] at he
    change (fun i ↦ A' i 0) = A.mulVec u at he
    exact he
  refine ⟨A', B', hBA', hRA', ?_⟩
  rw [hcol]
  exact hcu

end PfaffianDescent
