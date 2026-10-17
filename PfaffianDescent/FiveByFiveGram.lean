import PfaffianDescent.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R]

/-- The Gram matrix of a degree-two socle pairing over a polynomial parameter.
The last row and column may contain arbitrary parameter-dependent entries. -/
def fiveByFiveGram (v : Fin 3 → R) (w : R) : Mat R 5 :=
  ![![0,0,0,0,1], ![0,-3,1,1,v 0], ![0,1,-3,1,v 1],
    ![0,1,1,-3,v 2], ![1,v 0,v 1,v 2,w]]

private def gramMinor (v : Fin 3 → R) : Mat R 4 :=
  ![![0,-3,1,1], ![0,1,-3,1], ![0,1,1,-3], ![1,v 0,v 1,v 2]]

private lemma gramMinor_det (v : Fin 3 → R) : (gramMinor v).det = 16 := by
  have hm : (gramMinor v).submatrix (3 : Fin 4).succAbove Fin.succ =
      (!![-3,1,1;1,-3,1;1,1,-3] : Mat R 3) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_column_zero, Finset.sum_eq_single (3 : Fin 4)]
  · have hp : (-1 : R) ^ ((3 : Fin 4) : ℕ) = -1 := by norm_num
    rw [hp]
    change -1 * 1 * ((gramMinor v).submatrix (3 : Fin 4).succAbove Fin.succ).det = 16
    rw [hm, Matrix.det_fin_three]
    change (-1 : R) * 1 *
      ((-3)*(-3)*(-3) - (-3)*1*1 - 1*1*(-3) + 1*1*1 + 1*1*1 - 1*(-3)*1) = 16
    ring
  · intro j _ hj
    have hz : gramMinor v j 0 = 0 := by
      fin_cases j <;> first | rfl | exact False.elim (hj rfl)
    rw [hz, mul_zero, zero_mul]
  · simp

/-- The parameter-dependent terms do not change the determinant. -/
lemma fiveByFiveGram_det (v : Fin 3 → R) (w : R) : (fiveByFiveGram v w).det = 16 := by
  have hm : (fiveByFiveGram v w).submatrix Fin.succ (4 : Fin 5).succAbove = gramMinor v := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (4 : Fin 5)]
  · have hp : (-1 : R) ^ ((4 : Fin 5) : ℕ) = 1 := by norm_num
    rw [hp]
    change 1 * 1 * ((fiveByFiveGram v w).submatrix Fin.succ (4 : Fin 5).succAbove).det = 16
    rw [hm, gramMinor_det]
    ring
  · intro j _ hj
    have hz : fiveByFiveGram v w 0 j = 0 := by
      fin_cases j <;> first | rfl | exact False.elim (hj rfl)
    rw [hz, mul_zero, zero_mul]
  · simp

end
end PfaffianDescent
