import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFractionTensorField
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Native right-field degree of the retained support tensor -/
noncomputable section
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def serreIncidenceSupportTensorRightEquiv
    {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F] :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := F)
    (L ⊗[K] F) ≃ₐ[F] (F ⊗[K] L) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := F)
  exact { __ := (Algebra.TensorProduct.comm K L F).toRingEquiv
          commutes' := fun f => by
            change (Algebra.TensorProduct.comm K L F) (1 ⊗ₜ[K] f) = f ⊗ₜ[K] 1
            simp }

theorem serreIncidenceSupportTensorRight_finrank
    {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F] :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := F)
    Module.finrank F (L ⊗[K] F) = Module.finrank K L := by
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := F)
  rw [(serreIncidenceSupportTensorRightEquiv (K := K) (L := L) (F := F)).toLinearEquiv.finrank_eq]
  exact Module.finrank_baseChange

theorem serreIncidenceSupportTensorRight_finite
    {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    [Module.Finite K L] :
    letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := F)
    Module.Finite F (L ⊗[K] F) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := F)
  exact Module.Finite.equiv
    (serreIncidenceSupportTensorRightEquiv (K := K) (L := L) (F := F)).symm.toLinearEquiv

end PfaffianDescent
