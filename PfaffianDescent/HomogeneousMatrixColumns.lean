import PfaffianDescent.HomogeneousProjection
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K σ m n : Type*} [Field K] [Fintype n]

/-- A polynomial matrix whose entire kernel is generated in positive degree
has linearly independent columns over the coefficient field. -/
theorem matrix_columns_independent_of_positive_kernel
    (A : Matrix m n (MvPolynomial σ K)) (q : n → MvPolynomial σ K) (j : n) (d : ℕ)
    (hd : 0 < d) (hq : (q j).IsHomogeneous d) (hne : q j ≠ 0)
    (hk : ∀ v, A.mulVec v = 0 → ∃ r : MvPolynomial σ K, v = r • q) :
    LinearIndependent K (fun i => fun k => A k i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hv : A.mulVec (fun k => C (c k)) = 0 := by
    funext k
    have h := congrFun hc k
    simp only [Finset.sum_apply, Pi.smul_apply, MvPolynomial.smul_eq_C_mul] at h
    change (∑ t, A k t * C (c t)) = 0
    simpa only [mul_comm, Pi.zero_apply] using h
  obtain ⟨r, hr⟩ := hk _ hv
  have hh : (r * q j).IsHomogeneous 0 := by
    have hj := congrFun hr j
    change C (c j) = r * q j at hj
    rw [← hj]
    exact isHomogeneous_C _ _
  have hz : r = 0 := eq_zero_of_mul_homogeneous_lt hq hne hh hd
  have hi := congrFun hr i
  simp only [hz, zero_smul, Pi.zero_apply] at hi
  exact MvPolynomial.C_injective σ K (hi.trans (map_zero C).symm)

end
end PfaffianDescent
