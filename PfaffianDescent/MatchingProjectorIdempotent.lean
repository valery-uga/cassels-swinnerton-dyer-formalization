import PfaffianDescent.BasisMatchingProjectorWholeUnionIdeal
import PfaffianDescent.ActualMatchingQuadraticLineKernelBasis
import Mathlib.LinearAlgebra.Projection

/-! SOURCE ONLY, UNVERIFIED. Idempotence descends through coefficient
injection. No idempotent/projection certificate is a final matching input. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]

theorem matchingEdgeProjectorMatrix_idempotent
    (B : Basis (Fin 4) K (Fin 4 → K)) :
    matchingEdgeProjectorMatrix B * matchingEdgeProjectorMatrix B =
      matchingEdgeProjectorMatrix B := by
  classical
  let M := basisCoordinateMatrix B
  let D : Matrix (Fin 4) (Fin 4) K := Matrix.diagonal ![1, 1, 0, 0]
  have hM : IsUnit M.det := basisCoordinateMatrix_isUnit B
  have hD : D * D = D := by
    ext m n
    fin_cases m <;> fin_cases n <;>
      simp [D, Matrix.mul_apply, Matrix.diagonal, Fin.sum_univ_four]
  rw [matchingEdgeProjectorMatrix_factor B]
  change (M * D * M⁻¹) * (M * D * M⁻¹) = M * D * M⁻¹
  calc
    (M * D * M⁻¹) * (M * D * M⁻¹) =
        (M * D) * (M⁻¹ * M) * (D * M⁻¹) := by noncomm_ring
    _ = M * (D * D) * M⁻¹ := by
      rw [Matrix.nonsing_inv_mul M hM, mul_one]
      noncomm_ring
    _ = M * D * M⁻¹ := by rw [hD]

theorem intermediateMatchingProjector_idempotent
    (E : IntermediateField k K) (P : Matrix (Fin 4) (Fin 4) E)
    (B : Basis (Fin 4) K (Fin 4 → K))
    (hP : P.map E.val.toRingHom = matchingEdgeProjectorMatrix B) : P * P = P := by
  apply Matrix.map_injective E.val.injective
  change (P * P).map E.val.toRingHom = P.map E.val.toRingHom
  rw [Matrix.map_mul, hP, matchingEdgeProjectorMatrix_idempotent B]

theorem idempotentMatrix_mulVecLin {E : Type u} [Field E]
    (P : Matrix (Fin 4) (Fin 4) E) (hP : P * P = P) :
    IsIdempotentElem P.mulVecLin := by
  change P.mulVecLin * P.mulVecLin = P.mulVecLin
  apply LinearMap.ext
  intro w
  change P.mulVec (P.mulVec w) = P.mulVec w
  rw [Matrix.mulVec_mulVec, hP]

/-- Derived complementary kernel decomposition, including characteristic 2. -/
theorem idempotentMatrix_isCompl_kernels {E : Type u} [Field E]
    (P : Matrix (Fin 4) (Fin 4) E) (hP : P * P = P) :
    IsCompl (LinearMap.ker (1 - P).mulVecLin) (LinearMap.ker P.mulVecLin) := by
  have hp := idempotentMatrix_mulVecLin P hP
  have hComp : (1 - P.mulVecLin) = (1 - P).mulVecLin := by
    apply LinearMap.ext
    intro w
    simp only [LinearMap.sub_apply, Module.End.one_apply, Matrix.mulVecLin_apply,
      Matrix.sub_mulVec, Matrix.one_mulVec]
  have h := LinearMap.IsIdempotentElem.isCompl hp
  rw [LinearMap.IsIdempotentElem.range_eq_ker_one_sub hp, hComp] at h
  exact h

end PfaffianDescent.QuarticNet
