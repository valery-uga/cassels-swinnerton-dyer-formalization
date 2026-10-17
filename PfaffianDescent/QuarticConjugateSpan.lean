import PfaffianDescent.QuarticEmbeddingAction
import Mathlib.RingTheory.Discriminant

/-!
# The conjugates of a residue-field basis span the geometric coordinates

Separability makes the discriminant nonzero.  Its embeddings-matrix formula
then proves that the four conjugates of any degree-four residue-field basis
form a basis after passing to an algebraically closed field.
-/

namespace PfaffianDescent
namespace QuarticNet

open Module

universe u

variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K]

theorem conjugate_basis_span [IsAlgClosed K] [FiniteDimensional k L]
    [Algebra.IsSeparable k L] (b : Basis (Fin 4) k L)
    (e : Fin 4 ≃ (L →ₐ[k] K)) :
    Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (b i))) = ⊤ := by
  let M : Matrix (Fin 4) (Fin 4) K := fun i j => e i (b j)
  have hdisc : Algebra.discr k b ≠ 0 := Algebra.discr_not_zero_of_basis k b
  have hmap : algebraMap k K (Algebra.discr k b) ≠ 0 :=
    (map_ne_zero (algebraMap k K)).mpr hdisc
  have hedet : (Algebra.embeddingsMatrixReindex k K b e).det ≠ 0 := by
    intro hz
    apply hmap
    rw [Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two k K b e, hz]
    simp
  have hM : M = (Algebra.embeddingsMatrixReindex k K b e).transpose := by
    ext i j
    rfl
  have hMdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_transpose]
    exact hedet
  have hlin : LinearIndependent K (fun i => M i) :=
    Matrix.linearIndependent_rows_of_det_ne_zero hMdet
  let B : Basis (Fin 4) K (Fin 4 → K) :=
    basisOfLinearIndependentOfCardEqFinrank hlin (by simp)
  have hspanM : Submodule.span K (Set.range (fun i => M i)) = ⊤ := by
    simpa [B] using B.span_eq
  have hrange : Set.range (fun i => M i) =
      Set.range (fun σ : L →ₐ[k] K => fun j => σ (b j)) := by
    exact e.surjective.range_comp (fun σ : L →ₐ[k] K => fun j => σ (b j))
  rw [← hrange]
  exact hspanM

end QuarticNet
end PfaffianDescent
