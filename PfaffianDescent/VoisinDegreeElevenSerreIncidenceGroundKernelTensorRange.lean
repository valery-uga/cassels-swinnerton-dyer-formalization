import PfaffianDescent.VoisinDegreeElevenSerreIncidenceGroundTensorMatrixColumns
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeKernelColumnsRange

/-! # Actual kernel tensor transport identifies the mapped ground frame with the native kernel -/
noncomputable section
open scoped TensorProduct
namespace PfaffianDescent
open Module
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceGroundKernelTensor_range
    {K F E V W T Q : Type u} [Field K] [Field F] [Field E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module F W]
    [AddCommGroup T] [Module F T] [AddCommGroup Q] [Module E Q]
    (frame : F ⊗[K] V ≃ₗ[F] W) (b : Basis (Fin 9) K V)
    (f : W →ₗ[F] T) (bk : Basis (Fin 3) F (LinearMap.ker f))
    (g : E ⊗[K] V →ₗ[E] Q)
    (κ : E ⊗[F] LinearMap.ker f ≃ₗ[E] LinearMap.ker g)
    (hκ : ∀ s : LinearMap.ker f,
      (κ (1 ⊗ₜ[F] s) : E ⊗[K] V) =
        serreIncidenceGroundTensorFrame (E := E) frame (1 ⊗ₜ[F] (s : W)))
    (coord : Q ≃ₗ[E] (Fin 6 → E)) (A : Matrix (Fin 6) (Fin 9) E)
    (hA : ∀ t, Matrix.toLin' A ((b.baseChange E).equivFun t) = coord (g t)) :
    LinearMap.range (Matrix.toLin'
      ((serreIncidenceGroundKernelMatrix f ((b.baseChange F).map frame) bk).map
        (algebraMap F E))) = LinearMap.ker (Matrix.toLin' A) := by
  let bE := (bk.baseChange E).map κ
  apply serreIncidenceNativeKernelColumns_range g (b.baseChange E) coord bE A _ hA
  intro i k
  rw [serreIncidenceGroundTensorMatrix_column]
  change _ = (b.baseChange E).equivFun (κ ((bk.baseChange E) k) : E ⊗[K] V) i
  rw [Basis.baseChange_apply, hκ]

end PfaffianDescent
