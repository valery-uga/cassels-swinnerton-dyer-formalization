import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! # Native field tensor of a geometrically integral affine fraction field -/
noncomputable section
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceFractionTensor_isDomain
    {K L R F : Type u} [Field K] [Field L] [CommRing R] [IsDomain R] [Field F]
    [Algebra K L] [Algebra K R] [Algebra K F] [Algebra R F]
    [IsScalarTower K R F] [IsFractionRing R F] [IsDomain (L ⊗[K] R)] :
    IsDomain (L ⊗[K] F) := by
  let t : (L ⊗[K] R) →ₐ[L] (L ⊗[K] F) :=
    Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom K R F)
  letI : Algebra (L ⊗[K] R) (L ⊗[K] F) := t.toRingHom.toAlgebra
  letI : IsScalarTower L (L ⊗[K] R) (L ⊗[K] F) :=
    IsScalarTower.of_algebraMap_eq' t.comp_algebraMap.symm
  let M := (nonZeroDivisors R).map
    (Algebra.TensorProduct.includeRight (R := K) (A := L)).toMonoidHom
  have H : (algebraMap (L ⊗[K] R) (L ⊗[K] F)).comp
        (Algebra.TensorProduct.includeRight (R := K) (A := L)).toRingHom =
      (Algebra.TensorProduct.includeRight (R := K) (A := L)).toRingHom.comp
        (algebraMap R F) := by
    ext r
    change t (1 ⊗ₜ[K] r) = 1 ⊗ₜ[K] (algebraMap R F) r
    rfl
  letI : IsLocalization M (L ⊗[K] F) :=
    IsLocalization.tensorProduct_tensorProduct_right K L (nonZeroDivisors R) F H
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (M := M) (L ⊗[K] F)
  intro x hx
  obtain ⟨r,hr,rfl⟩ := hx
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  intro hzero
  have hi := Algebra.TensorProduct.includeRight_injective
    (B := R) (FaithfulSMul.algebraMap_injective K L)
  apply nonZeroDivisors.ne_zero hr
  exact hi (by simpa using hzero)

end PfaffianDescent
