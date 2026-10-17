import PfaffianDescent.MatchingProjectorIdempotent
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-! SOURCE ONLY, UNVERIFIED. Construct the frame OVER E itself from the
actual two complementary rank-two kernels. Never lift a K-frame to E. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module
open scoped BigOperators
universe u
variable {E : Type u} [Field E]

def idempotentTwoKernelFrame
    (P : Matrix (Fin 4) (Fin 4) E) (hP : P * P = P)
    (b : Basis (Fin 2) E (LinearMap.ker (1 - P).mulVecLin))
    (c : Basis (Fin 2) E (LinearMap.ker P.mulVecLin)) :
    Basis (Fin 4) E (Fin 4 → E) :=
  ((b.prod c).map (Submodule.prodEquivOfIsCompl _ _
    (idempotentMatrix_isCompl_kernels P hP))).reindex finSumFinEquiv

theorem idempotentTwoKernelFrame_left
    (P : Matrix (Fin 4) (Fin 4) E) (hP : P * P = P)
    (b : Basis (Fin 2) E (LinearMap.ker (1 - P).mulVecLin))
    (c : Basis (Fin 2) E (LinearMap.ker P.mulVecLin)) (i : Fin 2) :
    idempotentTwoKernelFrame P hP b c (Fin.castAdd 2 i) = (b i : Fin 4 → E) := by
  simp only [idempotentTwoKernelFrame, Basis.reindex_apply, Basis.map_apply]
  rw [finSumFinEquiv_symm_apply_castAdd (n := 2) i]
  simp [Basis.prod_apply]

theorem idempotentTwoKernelFrame_right
    (P : Matrix (Fin 4) (Fin 4) E) (hP : P * P = P)
    (b : Basis (Fin 2) E (LinearMap.ker (1 - P).mulVecLin))
    (c : Basis (Fin 2) E (LinearMap.ker P.mulVecLin)) (i : Fin 2) :
    idempotentTwoKernelFrame P hP b c (Fin.natAdd 2 i) = (c i : Fin 4 → E) := by
  simp only [idempotentTwoKernelFrame, Basis.reindex_apply, Basis.map_apply]
  rw [finSumFinEquiv_symm_apply_natAdd (m := 2) i]
  simp [Basis.prod_apply]

/-- An edge projector fixes its first two basis vectors and kills the other two. -/
theorem matchingEdgeProjectorMatrix_mulVec_basis
    (B : Basis (Fin 4) E (Fin 4 → E)) (i : Fin 4) :
    (matchingEdgeProjectorMatrix B).mulVec (B i) =
      (if i = 0 ∨ i = 1 then B i else 0) := by
  classical
  let M := basisCoordinateMatrix B
  let D : Matrix (Fin 4) (Fin 4) E := Matrix.diagonal ![1, 1, 0, 0]
  have hM : IsUnit M.det := basisCoordinateMatrix_isUnit B
  have hcol : M.mulVec (Pi.single i (1 : E)) = B i := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hinv : M⁻¹.mulVec (B i) = Pi.single i 1 := by
    rw [← hcol, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hM,
      Matrix.one_mulVec]
  rw [matchingEdgeProjectorMatrix_factor B]
  change (M * D * M⁻¹).mulVec (B i) = _
  rw [← Matrix.mulVec_mulVec, hinv, ← Matrix.mulVec_mulVec]
  fin_cases i <;> simp [D, Matrix.diagonal_mulVec_single, M,
    basisCoordinateMatrix, Matrix.col_apply] <;> rfl

theorem idempotentTwoKernelFrame_projector
    (P : Matrix (Fin 4) (Fin 4) E) (hP : P * P = P)
    (b : Basis (Fin 2) E (LinearMap.ker (1 - P).mulVecLin))
    (c : Basis (Fin 2) E (LinearMap.ker P.mulVecLin)) :
    matchingEdgeProjectorMatrix (idempotentTwoKernelFrame P hP b c) = P := by
  classical
  let B := idempotentTwoKernelFrame P hP b c
  have hLeft (i : Fin 2) : P.mulVec (b i : Fin 4 → E) = (b i : Fin 4 → E) := by
    have h := (b i).property
    change (1 - P).mulVec (b i : Fin 4 → E) = 0 at h
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h
    exact (sub_eq_zero.mp h).symm
  have hRight (i : Fin 2) : P.mulVec (c i : Fin 4 → E) = 0 := (c i).property
  have hlin : (matchingEdgeProjectorMatrix B).mulVecLin = P.mulVecLin := by
    apply B.ext
    intro i
    change (matchingEdgeProjectorMatrix B).mulVec (B i) = P.mulVec (B i)
    rw [matchingEdgeProjectorMatrix_mulVec_basis]
    have h0 : B 0 = (b 0 : Fin 4 → E) := idempotentTwoKernelFrame_left P hP b c 0
    have h1 : B 1 = (b 1 : Fin 4 → E) := idempotentTwoKernelFrame_left P hP b c 1
    have h2 : B 2 = (c 0 : Fin 4 → E) := idempotentTwoKernelFrame_right P hP b c 0
    have h3 : B 3 = (c 1 : Fin 4 → E) := idempotentTwoKernelFrame_right P hP b c 1
    fin_cases i <;> simp [h0, h1, h2, h3, hLeft, hRight]
  apply Matrix.mulVec_injective
  exact congrArg (fun f : (Fin 4 → E) →ₗ[E] (Fin 4 → E) => (f : _ → _)) hlin

/-- Structural specialization for the actual E/P already derived from the
matching presentation. Kernel dimensions/bases and idempotence are internal. -/
theorem intermediateMatchingLine_has_projectiveFrame
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (E : IntermediateField k K) (P : Matrix (Fin 4) (Fin 4) E)
    (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B) :
    ∃ C : Basis (Fin 4) E (Fin 4 → E), matchingEdgeProjectorMatrix C = P := by
  classical
  have hIdem := intermediateMatchingProjector_idempotent E P B hP
  let b := Module.finBasisOfFinrankEq E _
    (intermediateMatchingLine_kernel_rank_two E P B hP)
  let c := Module.finBasisOfFinrankEq E _
    (intermediateMatchingOtherLine_kernel_rank_two E P B hP)
  exact ⟨idempotentTwoKernelFrame P hIdem b c,
    idempotentTwoKernelFrame_projector P hIdem b c⟩

end PfaffianDescent.QuarticNet
