import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Quotient.Operations

/- SOURCE ONLY / UNVERIFIED. Tensoring the ACTUAL residue ideal by its
actual surjective residue ring gives I/I^2, with literal 1 tensor x formula.
No conormal/tensor comparison certificate is supplied. -/
noncomputable section
namespace PfaffianDescent
open scoped TensorProduct
universe u

def surjectiveResidueTensorConormalEquiv
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho) :
    letI : Algebra R L := rho.toAlgebra
    L ⊗[R] RingHom.ker rho ≃ₗ[R] (RingHom.ker rho).Cotangent := by
  letI : Algebra R L := rho.toAlgebra
  let e : (R ⧸ RingHom.ker rho) ≃ₐ[R] L :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R L) hrho
  exact (TensorProduct.congr e.symm.toLinearEquiv
    (LinearEquiv.refl R (RingHom.ker rho))).trans
      (TensorProduct.quotTensorEquivQuotSMul (RingHom.ker rho) (RingHom.ker rho))

@[simp] lemma surjectiveResidueTensorConormalEquiv_one_tmul
    {R L : Type u} [CommRing R] [CommRing L]
    (rho : R →+* L) (hrho : Function.Surjective rho) (x : RingHom.ker rho) :
    letI : Algebra R L := rho.toAlgebra
    surjectiveResidueTensorConormalEquiv rho hrho ((1 : L) ⊗ₜ[R] x) =
      (RingHom.ker rho).toCotangent x := by
  letI : Algebra R L := rho.toAlgebra
  let e : (R ⧸ RingHom.ker rho) ≃ₐ[R] L :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R L) hrho
  let a := TensorProduct.congr e.symm.toLinearEquiv
    (LinearEquiv.refl R (RingHom.ker rho))
  let b := TensorProduct.quotTensorEquivQuotSMul (RingHom.ker rho) (RingHom.ker rho)
  change b (a ((1 : L) ⊗ₜ[R] x)) = _
  have he : e.symm.toLinearEquiv (1 : L) = (1 : R ⧸ RingHom.ker rho) :=
    e.symm.map_one
  have ha : a ((1 : L) ⊗ₜ[R] x) = (1 : R ⧸ RingHom.ker rho) ⊗ₜ[R] x :=
    (TensorProduct.congr_tmul e.symm.toLinearEquiv
      (LinearEquiv.refl R (RingHom.ker rho)) (1 : L) x).trans
      (congrArg (fun z : R ⧸ RingHom.ker rho => z ⊗ₜ[R] x) he)
  exact (congrArg b ha).trans
    (TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (RingHom.ker rho) x)

end PfaffianDescent
