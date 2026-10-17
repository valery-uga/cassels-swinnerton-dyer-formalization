import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFractionTensorDomain
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # A finite original field retains its full field tensor over a regular fraction field -/
noncomputable section
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceFractionTensor_isField
    {K L R F : Type u} [Field K] [Field L] [CommRing R] [IsDomain R] [Field F]
    [Algebra K L] [Algebra K R] [Algebra K F] [Algebra R F]
    [IsScalarTower K R F] [IsFractionRing R F] [IsDomain (L ⊗[K] R)]
    [Module.Finite K L] : IsField (L ⊗[K] F) := by
  letI : IsDomain (L ⊗[K] F) := serreIncidenceFractionTensor_isDomain (K := K) (L := L) (R := R) (F := F)
  let e := Algebra.TensorProduct.comm K L F
  letI : IsDomain (F ⊗[K] L) := Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  have hf := IsField.of_isDomain_of_finite F (F ⊗[K] L)
  exact { exists_pair_ne := Nontrivial.exists_pair_ne
          mul_comm := mul_comm
          mul_inv_cancel := by
            intro x hx
            have hex : e x ≠ 0 := by
              intro h
              apply hx
              exact e.injective (by simpa using h)
            obtain ⟨y,hy⟩ := hf.mul_inv_cancel hex
            refine ⟨e.symm y, e.injective ?_⟩
            simpa only [map_mul, e.apply_symm_apply, map_one] using hy }

end PfaffianDescent
