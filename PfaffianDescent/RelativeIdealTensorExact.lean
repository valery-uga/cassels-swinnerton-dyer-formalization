import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Exact base change for an ideal with a relatively flat quotient

The parameter change itself need not be flat.  When `A ⧸ I` is flat over
the parameter ring `R`, the sequence `0 → I → A → A ⧸ I → 0` stays exact
after tensoring with any `R`-module.  This is the affine algebra needed to
compare the universal divisor ideal with ideals in nonflat parameter fibres.
-/

namespace PfaffianDescent

open scoped TensorProduct

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup B] [Module R B]

/-- Relative flatness of the quotient makes the base-changed inclusion of
the ideal injective, even when the change-of-parameters module is not flat. -/
theorem relativeIdeal_lTensor_injective_of_quotient_flat
    (I : Ideal A) [Module.Flat R (A ⧸ I)] :
    Function.Injective (((I.restrictScalars R).subtype).lTensor B) := by
  haveI : Module.Flat R (A ⧸ I.restrictScalars R) :=
    Module.Flat.of_linearEquiv (Submodule.Quotient.restrictScalarsEquiv R I)
  exact LinearMap.lTensor_injective_of_exact_of_flat
    (I.restrictScalars R).mkQ (Submodule.mkQ_surjective _)
    (I.restrictScalars R).subtype (Submodule.subtype_injective _)
    (LinearMap.exact_subtype_mkQ _) B

/-- The kernel of the tensor-changed quotient map is canonically the tensor
change of the ideal itself.  This is the full exactness statement behind the
preceding injectivity theorem. -/
noncomputable def relativeIdeal_tensorKernelEquiv_of_quotient_flat
    (I : Ideal A) [Module.Flat R (A ⧸ I)] :
    LinearMap.ker (((I.restrictScalars R).mkQ).lTensor B) ≃ₗ[R]
      B ⊗[R] (I.restrictScalars R) := by
  haveI : Module.Flat R (A ⧸ I.restrictScalars R) :=
    Module.Flat.of_linearEquiv (Submodule.Quotient.restrictScalarsEquiv R I)
  let e := ((I.restrictScalars R).mkQ).kerLTensorEquivOfSurjective
    (Submodule.mkQ_surjective _) B
  have hker : LinearMap.ker ((I.restrictScalars R).mkQ) =
      I.restrictScalars R := Submodule.ker_mkQ _
  rw [hker] at e
  exact e

/-- The quotient of the source of a surjective algebra map is flat over
the parameter ring whenever its target is flat.  This connects the
ideal-quotient formulation above to actual affine chart quotient maps. -/
theorem relativeSurjectiveAlgebraHom_quotientKer_flat
    {C : Type u} [CommRing C] [Algebra R C]
    (f : A →ₐ[R] C) (hf : Function.Surjective f)
    [Module.Flat R C] :
    Module.Flat R (A ⧸ RingHom.ker f.toRingHom) := by
  let e : (A ⧸ RingHom.ker f.toRingHom) ≃ₐ[R] C :=
    AlgEquiv.ofRingEquiv
      (f := f.toRingHom.quotientKerEquivOfSurjective hf) (by
        intro r
        change f (algebraMap R A r) = algebraMap R C r
        exact f.commutes r)
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-- The kernel of a surjective algebra map to a relatively flat target
remains embedded in the source after tensoring with any parameter module.
The parameter change itself need not be flat. -/
theorem relativeSurjectiveAlgebraHom_kernel_lTensor_injective
    {C : Type u} [CommRing C] [Algebra R C]
    (f : A →ₐ[R] C) (hf : Function.Surjective f)
    [Module.Flat R C] :
    Function.Injective
      ((((RingHom.ker f.toRingHom).restrictScalars R).subtype).lTensor B) := by
  haveI : Module.Flat R (A ⧸ RingHom.ker f.toRingHom) :=
    relativeSurjectiveAlgebraHom_quotientKer_flat f hf
  exact relativeIdeal_lTensor_injective_of_quotient_flat
    (RingHom.ker f.toRingHom)

/-- The full tensor-kernel comparison for a surjective relatively flat
affine chart quotient. -/
noncomputable def relativeSurjectiveAlgebraHom_tensorKernelEquiv
    {C : Type u} [CommRing C] [Algebra R C]
    (f : A →ₐ[R] C) (hf : Function.Surjective f)
    [Module.Flat R C] :
    LinearMap.ker
        ((((RingHom.ker f.toRingHom).restrictScalars R).mkQ).lTensor B) ≃ₗ[R]
      B ⊗[R] ((RingHom.ker f.toRingHom).restrictScalars R) := by
  haveI : Module.Flat R (A ⧸ RingHom.ker f.toRingHom) :=
    relativeSurjectiveAlgebraHom_quotientKer_flat f hf
  exact relativeIdeal_tensorKernelEquiv_of_quotient_flat
    (RingHom.ker f.toRingHom)

/-- For the actual surjective chart map, rather than its canonical quotient
presentation, the kernel after tensor change is the tensor change of the
original kernel. -/
noncomputable def relativeSurjectiveAlgebraHom_actualTensorKernelEquiv
    {C : Type u} [CommRing C] [Algebra R C]
    (f : A →ₐ[R] C) (hf : Function.Surjective f)
    [Module.Flat R C] :
    LinearMap.ker (f.toLinearMap.lTensor B) ≃ₗ[R]
      B ⊗[R] ((RingHom.ker f.toRingHom).restrictScalars R) := by
  let e := f.toLinearMap.kerLTensorEquivOfSurjective hf B
  have hker : LinearMap.ker f.toLinearMap =
      (RingHom.ker f.toRingHom).restrictScalars R := by
    ext a
    rfl
  rw [hker] at e
  exact e

end PfaffianDescent
