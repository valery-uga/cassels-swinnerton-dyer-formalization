import PfaffianDescent.PolynomialLinearChange
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Coefficients of a homogeneous plane equation

Every homogeneous degree-one equation is an explicit linear combination of
the four projective coordinates. This is the first step in constructing an
invertible coordinate change that sends an arbitrary plane to `X₀ = 0`.
-/

namespace PfaffianDescent

open MvPolynomial

universe u

theorem exists_linear_coefficients_of_homogeneous_one
    {K : Type u} [Field K]
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1) :
    ∃ a : Fin 4 → K,
      ell = ∑ i : Fin 4, C (a i) * X i := by
  have hspan : ell ∈ Submodule.span K
      (Set.range (X : Fin 4 → MvPolynomial (Fin 4) K)) := by
    rw [← MvPolynomial.homogeneousSubmodule_one_eq_span_X]
    exact hell
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hspan
  refine ⟨a, ?_⟩
  simpa only [smul_eq_C_mul] using ha.symm

theorem exists_nonzero_linear_coefficient_of_homogeneous_one
    {K : Type u} [Field K]
    (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0) :
    ∃ (a : Fin 4 → K) (i : Fin 4),
      ell = ∑ j : Fin 4, C (a j) * X j ∧ a i ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_linear_coefficients_of_homogeneous_one ell hell
  by_contra h
  push Not at h
  have hz : ∀ i : Fin 4, a i = 0 := by
    intro i
    by_contra hi
    exact hi (h a i ha)
  apply hell0
  simp [ha, hz]

/-- Replacing one identity-matrix row by a coefficient vector has determinant
equal to the coefficient in that row's column. -/
theorem det_identity_updateRow
    {K : Type u} [Field K] (a : Fin 4 → K) (i : Fin 4) :
    ((1 : Matrix (Fin 4) (Fin 4) K).updateRow i a).det = a i := by
  have hrow : a = ∑ j : Fin 4, (a j) • (1 : Matrix (Fin 4) (Fin 4) K) j := by
    funext k
    simp [Matrix.one_apply, Finset.sum_ite_eq']
  nth_rewrite 1 [hrow]
  rw [Matrix.det_updateRow_sum]
  simp

/-- Any coefficient vector with a nonzero entry can be the first row of
an invertible four-by-four matrix. -/
theorem exists_invertible_matrix_first_row
    {K : Type u} [Field K] (a : Fin 4 → K)
    (i : Fin 4) (hai : a i ≠ 0) :
    ∃ M : Matrix (Fin 4) (Fin 4) K,
      IsUnit M.det ∧ M 0 = a := by
  let N : Matrix (Fin 4) (Fin 4) K := (1 : Matrix (Fin 4) (Fin 4) K).updateRow i a
  let σ : Equiv.Perm (Fin 4) := Equiv.swap 0 i
  let M : Matrix (Fin 4) (Fin 4) K := N.submatrix σ id
  have hrow : M 0 = a := by
    funext j
    simp [M, N, σ]
  refine ⟨M, ?_, hrow⟩
  apply isUnit_iff_ne_zero.mpr
  change (N.submatrix σ id).det ≠ 0
  rw [Matrix.det_permute]
  have hN : N.det = a i := det_identity_updateRow a i
  rw [hN]
  have hsign : (↑↑(Equiv.Perm.sign σ) : K) ≠ 0 := by
    by_cases hi : (0 : Fin 4) = i
    · simp [σ, hi]
    · simp [σ, Equiv.Perm.sign_swap', hi]
  exact mul_ne_zero hsign hai

/-- Every nonzero homogeneous plane equation is the image of the standard
plane equation under an invertible linear coordinate substitution. -/
theorem exists_linear_change_for_plane_equation
    {K : Type u} [Field K]
    (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1) (hell0 : ell ≠ 0) :
    ∃ (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det),
      ell = linearSubstitutionEquiv M hM (X 0) := by
  obtain ⟨a, i, ha, hai⟩ :=
    exists_nonzero_linear_coefficient_of_homogeneous_one ell hell hell0
  obtain ⟨M, hM, hrow⟩ := exists_invertible_matrix_first_row a i hai
  refine ⟨M, hM, ?_⟩
  change ell = linearSubstitution M (X 0)
  rw [linearSubstitution_X]
  change ell = ∑ j : Fin 4, C (M 0 j) * X j
  simpa only [hrow] using ha

end PfaffianDescent
