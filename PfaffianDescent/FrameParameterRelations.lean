import PfaffianDescent.FrameCoordinateRingExact

namespace PfaffianDescent.FrameCoordinateRing
open scoped BigOperators
section
variable {K : Type*} [Field K]

/-- Multiplication by the regular linear parameter expresses all coordinate squares. -/
lemma ell_mul_x (i : Fin 4) : ell (K := K) * x i = x i ^ 2 + 3 * q := by
  classical
  have hs : ∑ j ∈ Finset.univ.erase i, x (K := K) j * x i = 3 * q := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i, q := by
        apply Finset.sum_congr rfl
        intro j hj
        exact mixed j i (Finset.mem_erase.mp hj).1
      _ = _ := by simp [nsmul_eq_mul]
  rw [ell, Finset.sum_mul, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), hs]
  ring

lemma x_sq_parameter (i : Fin 4) : x (K := K) i ^ 2 = ell * x i - 3 * q := by
  rw [ell_mul_x]
  ring

lemma x_three_parameter : x (K := K) 3 = ell - x 0 - x 1 - x 2 := by
  simp only [ell, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change x (K := K) 3 = x 0 + (x 1 + (x 2 + x 3)) - x 0 - x 1 - x 2
  ring

/-- All coordinate multiples of the mixed quadratic are one fourth of its parameter multiple. -/
lemma ell_mul_q (i : Fin 4) : ell (K := K) * q = 4 * (x i * q) := by
  rw [ell, Finset.sum_mul]
  calc
    _ = ∑ _j : Fin 4, x (K := K) i * q := by
      apply Finset.sum_congr rfl
      intro j _
      exact variable_mul_q_eq j i
    _ = _ := by simp [nsmul_eq_mul]

lemma q_sq_parameter : 16 * q (K := K) ^ 2 = ell ^ 2 * q := by
  calc
    _ = 4 * x (K := K) 0 * (4 * (x 1 * q)) := by rw [q]; ring
    _ = 4 * x (K := K) 0 * (ell * q) := by rw [← ell_mul_q 1]
    _ = ell * (4 * (x (K := K) 0 * q)) := by ring
    _ = ell ^ 2 * q := by rw [← ell_mul_q 0]; ring

lemma x_mul_q_parameter [CharZero K] (i : Fin 4) :
    x (K := K) i * q = (4 : K)⁻¹ • (ell * q) := by
  have h4 : (4 : K) ≠ 0 := by norm_num
  have he : (4 : K) • (x (K := K) i * q) = ell * q := by
    calc
      (4 : K) • (x (K := K) i * q) =
          algebraMap K (FrameCoordinateRing K) (4 : K) * (x i * q) := Algebra.smul_def _ _
      _ = 4 * (x i * q) := by rw [map_ofNat]
      _ = ell * q := (ell_mul_q (K := K) i).symm
  calc
    _ = ((4 : K)⁻¹ * 4) • (x (K := K) i * q) := by rw [inv_mul_cancel₀ h4, one_smul]
    _ = _ := by rw [mul_smul, he]

end
end PfaffianDescent.FrameCoordinateRing
