import PfaffianDescent.Isotropic
import Mathlib.Tactic.LinearCombination

namespace PfaffianDescent
open scoped BigOperators

section
variable {K : Type*} [Field K] [NeZero (2 : K)]

/-- The matrix and bilinear-form conventions agree on alternation. -/
theorem isAlt_toBilin (A : Mat K 6) (hA : IsAlternating A) :
    (Matrix.toBilin' A).IsAlt := by
  have ht : A.transpose = -A := by
    ext i j
    exact hA.2 i j
  intro v
  rw [Matrix.toBilin'_apply']
  have hh := Matrix.dotProduct_transpose_mulVec A v v
  rw [ht, Matrix.neg_mulVec, dotProduct_neg] at hh
  have hz : (2 : K) * (v ⬝ᵥ A.mulVec v) = 0 := by
    linear_combination -hh
  exact (mul_eq_zero.mp hz).resolve_left (NeZero.ne _)

omit [NeZero (2 : K)] in
/-- Linear combinations preserve alternation. -/
theorem isAlternating_pencil (A : Fin 4 → Mat K 6)
    (hA : ∀ i, IsAlternating (A i)) (x : Vec K 4) : IsAlternating (pencil A x) := by
  constructor
  · intro i
    simp only [pencil, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      (hA 0).1 i, (hA 1).1 i, (hA 2).1 i, (hA 3).1 i, mul_zero, add_zero]
  · intro i j
    simp only [pencil, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      (hA 0).2 i j, (hA 1).2 i j, (hA 2).2 i j, (hA 3).2 i j]
    ring

/-- Step 1's linear-algebra construction, including nonzero projective coordinates.
The existence of the common isotropic subspace is a separate input. -/
theorem pfaffian_point_of_isotropic_three_space (A : Fin 4 → Mat K 6)
    (hA : ∀ i, IsAlternating (A i))
    (W : Submodule K (Vec K 6)) (hW : Module.finrank K W = 3)
    (hiso : ∀ i : Fin 3, ∀ v w : W, (v : Vec K 6) ⬝ᵥ (A i.castSucc).mulVec w = 0) :
    HasPfaffianPoint A := by
  let B : Fin 4 → LinearMap.BilinForm K (Vec K 6) := fun i => Matrix.toBilin' (A i)
  obtain ⟨q, v, hq, hv, hzero⟩ := singular_combination_of_isotropic_three_space
    (show Module.finrank K (Vec K 6) = 6 by simp [Vec]) B
    (isAlt_toBilin (A 3) (hA 3)) W hW
    (fun i v w => by simpa only [B, Matrix.toBilin'_apply'] using hiso i v w)
  refine ⟨q, hq, pf6_eq_zero_of_kernel (pencil A q) (isAlternating_pencil A hA q) v hv ?_⟩
  funext j
  have hh := hzero (Pi.single j 1)
  simp only [B, Matrix.toBilin'_apply', single_one_dotProduct] at hh
  simpa only [pencil, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, Fin.sum_univ_four,
    Pi.zero_apply, add_assoc] using hh

end
end PfaffianDescent
