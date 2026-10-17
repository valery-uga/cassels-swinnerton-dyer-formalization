import PfaffianDescent.FlatInjectiveDimensionDescent
import PfaffianDescent.FrobeniusCoextension
import PfaffianDescent.PolynomialCoefficientRetraction
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Flat.Stability

namespace PfaffianDescent
open CategoryTheory ModuleCat TensorProduct
universe u
section
variable {K L A : Type u} [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A]

/-- Apply a coefficient functional on the field-extension factor of an algebraic tensor product. -/
noncomputable def fieldTensorRetraction (phi : L →ₗ[K] K) : A ⊗[K] L →ₗ[A] A :=
  (AlgebraTensorModule.rid K A A).toLinearMap.comp (AlgebraTensorModule.lTensor A A phi)

@[simp] lemma fieldTensorRetraction_tmul (phi : L →ₗ[K] K) (a : A) (l : L) :
    fieldTensorRetraction phi (a ⊗ₜ[K] l) = phi l • a := rfl

/-- Finite self-injective dimension descends from any extension of the ground field. -/
theorem field_tensor_self_injectiveDimensionLE (n : ℕ)
    [HasInjectiveDimensionLE (ModuleCat.of (A ⊗[K] L) (A ⊗[K] L)) n] :
    HasInjectiveDimensionLE (ModuleCat.of A A) n := by
  obtain ⟨phi, hphi⟩ := exists_field_linear_retraction (K := K) (L := L)
  have h1 : phi 1 = 1 := by simpa only [map_one] using hphi 1
  let r : (restrictScalars (algebraMap A (A ⊗[K] L))).obj
      (ModuleCat.of (A ⊗[K] L) (A ⊗[K] L)) →ₗ[A] A :=
    (fieldTensorRetraction phi).comp
      (restrictionRegularEquiv (R := A) (A := A ⊗[K] L)).toLinearMap
  apply split_flat_self_injectiveDimensionLE (algebraMap A (A ⊗[K] L))
    (RingHom.flat_algebraMap_iff.mpr inferInstance) r _ n
  intro a
  change fieldTensorRetraction phi (a ⊗ₜ[K] (1 : L)) = a
  rw [fieldTensorRetraction_tmul, h1, one_smul]

end
end PfaffianDescent
