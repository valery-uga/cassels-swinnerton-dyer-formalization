import PfaffianDescent.HomogeneousProjection
import Mathlib.Algebra.MvPolynomial.Division

namespace PfaffianDescent
open MvPolynomial
section
variable {K σ : Type*} [Field K]

/-- Set one polynomial variable equal to zero, retaining the other variables. -/
noncomputable def killVariable (i : σ) : MvPolynomial σ K →ₐ[K] MvPolynomial σ K := by
  classical
  exact MvPolynomial.aeval (fun j => if j = i then 0 else X j)

@[simp] lemma killVariable_C (i : σ) (a : K) : killVariable i (C a) = C a := by
  simp [killVariable]

@[simp] lemma killVariable_X_self (i : σ) : killVariable (K := K) i (X i) = 0 := by
  simp [killVariable]

@[simp] lemma killVariable_X_of_ne (i j : σ) (h : j ≠ i) :
    killVariable (K := K) i (X j) = X j := by
  simp [killVariable, h]

lemma killVariable_idempotent (i : σ) (p : MvPolynomial σ K) :
    killVariable i (killVariable i p) = killVariable i p := by
  have h : (killVariable (K := K) i).comp (killVariable i) = killVariable i := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  exact DFunLike.congr_fun h p

lemma killVariable_homogeneous (i : σ) {p : MvPolynomial σ K} {d : ℕ}
    (hp : p.IsHomogeneous d) : (killVariable i p).IsHomogeneous d := by
  classical
  have hx (j : σ) : (if j = i then 0 else X j : MvPolynomial σ K).IsHomogeneous 1 := by
    split_ifs
    · exact (homogeneousSubmodule σ K 1).zero_mem
    · exact isHomogeneous_X K j
  change (MvPolynomial.aeval (fun j => if j = i then 0 else X j) p).IsHomogeneous d
  simpa only [one_mul] using hp.aeval _ hx

/-- The difference from restriction to a coordinate hyperplane is divisible by
that coordinate. -/
lemma variable_dvd_sub_reduction (i : σ) (p : MvPolynomial σ K) :
    X i ∣ p - killVariable i p := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simpa only [map_add, add_sub_add_comm] using dvd_add hp hq
  | mul_X p j hp =>
    by_cases hj : j = i
    · subst j
      rw [map_mul, killVariable_X_self, mul_zero, sub_zero]
      exact dvd_mul_left _ _
    · rw [map_mul, killVariable_X_of_ne i j hj, ← sub_mul]
      exact dvd_mul_of_dvd_left hp _

/-- The kernel of restriction to a coordinate hyperplane is its principal ideal. -/
theorem variable_dvd_iff_reduction_zero (i : σ) (p : MvPolynomial σ K) :
    X i ∣ p ↔ killVariable i p = 0 := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [map_mul, killVariable_X_self, zero_mul]
  · intro h
    simpa only [h, sub_zero] using variable_dvd_sub_reduction i p

end
end PfaffianDescent
