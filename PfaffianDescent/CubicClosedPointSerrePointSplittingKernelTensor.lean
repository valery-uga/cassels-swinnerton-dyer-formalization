import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
open scoped TensorProduct
namespace PfaffianDescent
universe u

/-- Literal scalar-extension comparison for an actual restriction kernel. -/
def pointSplittingKernelTensorEquiv
    {F E V W : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (R : V →ₗ[F] W) :
    (E ⊗[F] LinearMap.ker R) ≃ₗ[E] LinearMap.ker (R.baseChange E) :=
  LinearMap.tensorKerEquiv E E R

theorem pointSplittingKernelTensorEquiv_tmul
    {F E V W : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (R : V →ₗ[F] W) (c : E) (s : LinearMap.ker R) :
    (pointSplittingKernelTensorEquiv R (c ⊗ₜ[F] s) : E ⊗[F] V) =
      c ⊗ₜ[F] (s : V) := rfl

end PfaffianDescent
