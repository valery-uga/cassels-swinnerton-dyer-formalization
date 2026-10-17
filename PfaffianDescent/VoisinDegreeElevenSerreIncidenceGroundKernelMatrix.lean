import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundKernelCoordinates
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelSchemeProjection

/-! # Actual ground restriction kernel columns give split projective equations -/
noncomputable section
namespace PfaffianDescent
open Module
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V]
variable {W : Type w} [AddCommGroup W] [Module F W]

def serreIncidenceGroundKernelMatrix (f : V →ₗ[F] W)
    (bV : Basis (Fin 9) F V) (bk : Basis (Fin 3) F (LinearMap.ker f)) :
    Matrix (Fin 9) (Fin 3) F :=
  LinearMap.toMatrix' (serreIncidenceGroundKernelInclusion f bV bk)

def serreIncidenceGroundEvaluationMatrix (f : V →ₗ[F] W)
    (bV : Basis (Fin 9) F V) (bW : Basis (Fin 6) F W) :
    Matrix (Fin 6) (Fin 9) F :=
  LinearMap.toMatrix' (serreIncidenceGroundEvaluationCoordinates f bV bW)

theorem serreIncidenceGroundKernelMatrix_exists_split (f : V →ₗ[F] W)
    (bV : Basis (Fin 9) F V) (bW : Basis (Fin 6) F W)
    (bk : Basis (Fin 3) F (LinearMap.ker f)) (honto : Function.Surjective f) :
    ∃ N : Matrix (Fin 3) (Fin 9) F, ∃ D : Matrix (Fin 9) (Fin 6) F,
      serreIncidenceGroundEvaluationMatrix f bV bW * serreIncidenceGroundKernelMatrix f bV bk = 0 ∧
      N * serreIncidenceGroundKernelMatrix f bV bk = 1 ∧
      serreIncidenceGroundKernelMatrix f bV bk * N +
        D * serreIncidenceGroundEvaluationMatrix f bV bW = 1 := by
  have hs : Function.Surjective (serreIncidenceGroundEvaluationCoordinates f bV bW) :=
    bW.equivFun.surjective.comp (honto.comp bV.equivFun.symm.surjective)
  obtain ⟨n, d, hfl, hnl, hsplit⟩ := serreIncidenceGroundKernel_exists_split
    (serreIncidenceGroundEvaluationCoordinates f bV bW)
    (serreIncidenceGroundKernelInclusion f bV bk)
    (serreIncidenceGroundKernelInclusion_range f bV bW bk)
    (serreIncidenceGroundKernelInclusion_injective f bV bk) hs
  refine ⟨LinearMap.toMatrix' n, LinearMap.toMatrix' d, ?_, ?_, ?_⟩
  · simpa only [serreIncidenceGroundEvaluationMatrix, serreIncidenceGroundKernelMatrix, LinearMap.toMatrix'_comp, map_zero] using
      congrArg LinearMap.toMatrix' hfl
  · simpa only [serreIncidenceGroundEvaluationMatrix, serreIncidenceGroundKernelMatrix, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] using
      congrArg LinearMap.toMatrix' hnl
  · simpa only [serreIncidenceGroundEvaluationMatrix, serreIncidenceGroundKernelMatrix, map_add, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] using
      congrArg LinearMap.toMatrix' hsplit

end PfaffianDescent
