import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundTensorFrameCoordinates
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundKernelColumns

/-! # Mapped ground kernel columns are literal original tensor-section coordinates -/
noncomputable section
open scoped TensorProduct
namespace PfaffianDescent
open Module
universe u v w z
set_option backward.isDefEq.respectTransparency false
variable {K F E : Type u} [Field K] [Field F] [Field E]
variable [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module F W]
variable {T : Type z} [AddCommGroup T] [Module F T]

theorem serreIncidenceGroundTensorMatrix_column
    (frame : F ⊗[K] V ≃ₗ[F] W) (b : Basis (Fin 9) K V)
    (f : W →ₗ[F] T) (bk : Basis (Fin 3) F (LinearMap.ker f))
    (i : Fin 9) (k : Fin 3) :
    (serreIncidenceGroundKernelMatrix f ((b.baseChange F).map frame) bk).map
      (algebraMap F E) i k =
    (b.baseChange E).equivFun
      (serreIncidenceGroundTensorFrame (E := E) frame (1 ⊗ₜ[F] (bk k : W))) i := by
  change algebraMap F E
    (serreIncidenceGroundKernelMatrix f ((b.baseChange F).map frame) bk i k) = _
  rw [serreIncidenceGroundKernelMatrix_column, serreIncidenceGroundTensorFrame_coordinates]
  simp only [Basis.equivFun_apply, Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

end PfaffianDescent
