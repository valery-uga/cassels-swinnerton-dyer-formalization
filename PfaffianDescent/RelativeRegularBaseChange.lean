import PfaffianDescent.RelativeIdealTensorExact
import PfaffianDescent.RegularPrincipalIdealFree

/-!
# Relative flatness preserves a regular equation under arbitrary base change

If `A/(z)` is flat over the parameter ring, the exact sequence cut out
by the regular equation `z` remains exact after tensoring with any
parameter algebra. Thus the changed equation remains regular without
flatness of the parameter change.
-/

namespace PfaffianDescent

open scoped TensorProduct

universe u

theorem tensor_regular_of_flat_principal_quotient
    {R A S : Type u} [CommRing R] [CommRing A] [CommRing S]
    [Algebra R A] [Algebra R S]
    (z : A) (hz : IsRegular z)
    [Module.Flat R (A ⧸ Ideal.span ({z} : Set A))] :
    IsRegular (1 ⊗ₜ[R] z : S ⊗[R] A) := by
  let I : Ideal A := Ideal.span ({z} : Set A)
  let e : A ≃ₗ[A] I := regularPrincipalIdealLinearEquiv z hz
  let eR : A ≃ₗ[R] I.restrictScalars R := e.restrictScalars R
  have hinj : Function.Injective (((I.restrictScalars R).subtype).lTensor S) :=
    relativeIdeal_lTensor_injective_of_quotient_flat (B := S) I
  have hinjMul : Function.Injective
      ((LinearMap.mulRight R z).lTensor S) := by
    have he : ((LinearMap.mulRight R z).lTensor S) =
        (((I.restrictScalars R).subtype).lTensor S).comp
          (eR.toLinearMap.lTensor S) := by
      apply LinearMap.ext
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul s a =>
          simp only [LinearMap.lTensor_tmul, LinearMap.comp_apply,
            LinearMap.mulRight_apply]
          change s ⊗ₜ[R] (a * z) =
            s ⊗ₜ[R] ((regularPrincipalIdealLinearEquiv z hz a).1)
          rfl
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [he]
    exact hinj.comp (eR.baseChange R S).injective
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  rw [mem_nonZeroDivisors_iff_left]
  intro t ht
  apply hinjMul
  have heval (t : S ⊗[R] A) : ((LinearMap.mulRight R z).lTensor S) t =
      t * (1 ⊗ₜ[R] z : S ⊗[R] A) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
      | tmul s a =>
        simp [LinearMap.lTensor_tmul, LinearMap.mulRight_apply,
          Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp [hx, hy, add_mul]
  rw [map_zero, heval]
  simpa only [mul_comm] using ht

end PfaffianDescent
