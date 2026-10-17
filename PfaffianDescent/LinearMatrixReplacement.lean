import PfaffianDescent.HomogeneousMatrixColumns
import Mathlib.LinearAlgebra.Dimension.Finite

namespace PfaffianDescent
open MvPolynomial Module
open scoped BigOperators
section
variable {K σ m n : Type*} [Field K] [Fintype n]

lemma linear_matrix_component (A : Matrix m n (MvPolynomial σ K))
    (hA : ∀ i j, (A i j).IsHomogeneous 1) (w : n → MvPolynomial σ K) (i : m) :
    A.mulVec (fun j => homogeneousComponent 0 (w j)) i = homogeneousComponent 1 (A.mulVec w i) := by
  change (∑ j, A i j * homogeneousComponent 0 (w j)) = homogeneousComponent 1 (∑ j, A i j * w j)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => (homogeneousComponent_mul_left (hA i j) 0).symm)

/-- The linear vectors in the polynomial image of a linear matrix are already
in the coefficient-field span of its columns. -/
theorem linear_matrix_range_mem_column_span (A : Matrix m n (MvPolynomial σ K))
    (hA : ∀ i j, (A i j).IsHomogeneous 1) (v : m → MvPolynomial σ K)
    (hv : ∀ i, (v i).IsHomogeneous 1) (hr : v ∈ LinearMap.range A.mulVecLin) :
    v ∈ Submodule.span K (Set.range A.col) := by
  obtain ⟨w, hw⟩ := hr
  have he : v = ∑ j, coeff 0 (w j) • A.col j := by
    funext i
    rw [Finset.sum_apply]
    calc
      v i = homogeneousComponent 1 (v i) := (homogeneousComponent_eq_self (hv i)).symm
      _ = homogeneousComponent 1 (A.mulVec w i) := by rw [← hw]; rfl
      _ = A.mulVec (fun j => homogeneousComponent 0 (w j)) i := (linear_matrix_component A hA w i).symm
      _ = ∑ j, (coeff 0 (w j) • A.col j) i := by
        simp only [Matrix.mulVec, dotProduct, homogeneousComponent_zero, Pi.smul_apply,
          MvPolynomial.smul_eq_C_mul, Matrix.col_apply, mul_comm]
  rw [he]
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self j)))

lemma polynomial_matrix_range_eq_of_column_span
    (A B : Matrix m n (MvPolynomial σ K))
    (h : Submodule.span K (Set.range A.col) = Submodule.span K (Set.range B.col)) :
    LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin := by
  rw [Matrix.range_mulVecLin, Matrix.range_mulVecLin,
    ← Submodule.span_span_of_tower K (MvPolynomial σ K) (Set.range A.col), h,
    Submodule.span_span_of_tower]

/-- Any independent set of the correct number of linear syzygies generates the
whole polynomial syzygy module once one linear generating matrix is known. -/
theorem linear_syzygy_matrix_replacement {P : Type*} [AddCommGroup P]
    [Module (MvPolynomial σ K) P]
    (f : (m → MvPolynomial σ K) →ₗ[MvPolynomial σ K] P)
    (A B : Matrix m n (MvPolynomial σ K))
    (hA : ∀ i j, (A i j).IsHomogeneous 1) (hB : ∀ i j, (B i j).IsHomogeneous 1)
    (hiA : LinearIndependent K A.col) (hiB : LinearIndependent K B.col)
    (hex : LinearMap.range A.mulVecLin = LinearMap.ker f)
    (hBker : ∀ j, f (B.col j) = 0) :
    LinearMap.range B.mulVecLin = LinearMap.ker f := by
  haveI : Module.Finite K (Submodule.span K (Set.range A.col)) :=
    Module.Finite.span_of_finite K (Set.finite_range _)
  have hspan : Submodule.span K (Set.range B.col) = Submodule.span K (Set.range A.col) := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro v ⟨j, rfl⟩
      apply linear_matrix_range_mem_column_span A hA (B.col j) (fun i => hB i j)
      rw [hex]
      exact hBker j
    · rw [finrank_span_eq_card hiB, finrank_span_eq_card hiA]
  exact (polynomial_matrix_range_eq_of_column_span B A hspan).trans hex

end
end PfaffianDescent
