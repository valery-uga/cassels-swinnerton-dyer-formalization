import PfaffianDescent.RelativeIdealTensorExact
import Mathlib.RingTheory.TensorProduct.Maps

/-! Compare linear and algebra tensor changes of a surjective algebra map. -/

namespace PfaffianDescent

open scoped TensorProduct

universe u

variable {R S A C : Type u}
  [CommRing R] [CommRing S] [CommRing A] [CommRing C]
  [Algebra R S] [Algebra R A] [Algebra R C]

/-- Tensoring an algebra map as a linear map agrees with its algebraic
coefficient-change map. -/
theorem algHom_lTensor_eq_tensorProductMap
    (f : A →ₐ[R] C) :
    f.toLinearMap.lTensor S =
      (Algebra.TensorProduct.map (AlgHom.id R S) f).toLinearMap := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s a =>
      simp only [LinearMap.lTensor_tmul, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply, AlgHom.toLinearMap_apply]
  | add x y hx hy => simpa [map_add, hx, hy]

/-- The kernel used in relative flatness is the underlying parameter
module of the ideal kernel of the algebraic tensor-changed map. -/
theorem algHom_lTensor_ker_eq_tensorProductMap_ker
    (f : A →ₐ[R] C) :
    LinearMap.ker (f.toLinearMap.lTensor S) =
      (RingHom.ker (Algebra.TensorProduct.map
        (AlgHom.id R S) f).toRingHom).restrictScalars R := by
  rw [algHom_lTensor_eq_tensorProductMap]
  ext x
  rfl

/-- If the quotient target is flat over the parameter ring, the actual
ideal kernel after algebraic coefficient change is the tensor extension
of the original ideal as an `R`-module. -/
noncomputable def relativeSurjectiveAlgebraHom_ringTensorKernelEquiv
    (f : A →ₐ[R] C) (hf : Function.Surjective f)
    [Module.Flat R C] :
    ((RingHom.ker (Algebra.TensorProduct.map
      (AlgHom.id R S) f).toRingHom).restrictScalars R) ≃ₗ[R]
      S ⊗[R] ((RingHom.ker f.toRingHom).restrictScalars R) := by
  exact (LinearEquiv.ofEq _ _
    (algHom_lTensor_ker_eq_tensorProductMap_ker (S := S) f).symm).trans
      (relativeSurjectiveAlgebraHom_actualTensorKernelEquiv (B := S) f hf)

/-- On a pure tensor, the inverse kernel equivalence has the expected
underlying tensor in the source ring. -/
theorem relativeSurjectiveAlgebraHom_ringTensorKernelEquiv_symm_tmul
    (f : A →ₐ[R] C) (hf : Function.Surjective f)
    [Module.Flat R C] (s : S)
    (x : (RingHom.ker f.toRingHom).restrictScalars R) :
    (((relativeSurjectiveAlgebraHom_ringTensorKernelEquiv (S := S) f hf).symm
      (s ⊗ₜ[R] x) : RingHom.ker
        (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom) :
      S ⊗[R] A) = s ⊗ₜ[R] (x : A) := by
  exact LinearMap.tensorKerEquivOfSurjective_symm_tmul
    f.toLinearMap hf S s x

end PfaffianDescent
