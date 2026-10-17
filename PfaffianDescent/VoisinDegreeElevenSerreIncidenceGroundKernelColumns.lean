import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundKernelMatrix

/-! # Ground kernel-frame columns are coordinates of literal kernel sections -/
noncomputable section
namespace PfaffianDescent
open Module
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V]
variable {W : Type w} [AddCommGroup W] [Module F W]

theorem serreIncidenceGroundKernelMatrix_column (f : V →ₗ[F] W)
    (bV : Basis (Fin 9) F V) (bk : Basis (Fin 3) F (LinearMap.ker f))
    (i : Fin 9) (k : Fin 3) :
    serreIncidenceGroundKernelMatrix f bV bk i k = bV.equivFun (bk k : V) i := by
  simp [serreIncidenceGroundKernelMatrix, LinearMap.toMatrix'_apply,
    serreIncidenceGroundKernelInclusion]

end PfaffianDescent
