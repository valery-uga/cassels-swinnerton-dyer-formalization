import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Cotangent

/-! Concrete representatives and zero tests for tensoring relations with a
quotient ring. These use the actual ideal submodule, not an assumed model. -/
namespace PfaffianDescent
open TensorProduct

variable {P : Type*} [CommRing P]

theorem residueTensor_exists_one_tmul316 (m : Ideal P)
    {M : Type*} [AddCommGroup M] [Module P M]
    (v : (P ⧸ m) ⊗[P] M) : ∃ x : M, v = 1 ⊗ₜ[P] x := by
  obtain ⟨x, hx⟩ := Submodule.mkQ_surjective (m • (⊤ : Submodule P M))
    (quotTensorEquivQuotSMul M m v)
  refine ⟨x, ?_⟩
  apply (quotTensorEquivQuotSMul M m).injective
  rw [quotTensorEquivQuotSMul_mk_one_tmul]
  exact hx.symm

theorem residueTensor_one_tmul_eq_zero316 (m : Ideal P)
    {M : Type*} [AddCommGroup M] [Module P M] (x : M) :
    (1 : P ⧸ m) ⊗ₜ[P] x = 0 ↔ x ∈ m • (⊤ : Submodule P M) := by
  constructor
  · intro h
    have he := congrArg (quotTensorEquivQuotSMul M m) h
    rw [quotTensorEquivQuotSMul_mk_one_tmul, map_zero] at he
    exact (Submodule.Quotient.mk_eq_zero _).mp he
  · intro h
    apply (quotTensorEquivQuotSMul M m).injective
    rw [quotTensorEquivQuotSMul_mk_one_tmul, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mpr h

theorem relation_mem_smul_top316 (m I : Ideal P) (x : I) :
    x ∈ m • (⊤ : Submodule P I) ↔ (x : P) ∈ m * I := by
  have hmap : (m • (⊤ : Submodule P I)).map I.subtype = m * I := by
    rw [Submodule.map_smul'' m ⊤ I.subtype, smul_eq_mul, Submodule.map_subtype_top]
  rw [← hmap]
  constructor
  · exact Submodule.mem_map_of_mem
  · intro h
    obtain ⟨y, hy, he⟩ := Submodule.mem_map.mp h
    have hxy : y = x := Subtype.ext he
    exact hxy ▸ hy

theorem residueTensor_relation_eq_zero316 (m I : Ideal P) (x : I) :
    (1 : P ⧸ m) ⊗ₜ[P] x = 0 ↔ (x : P) ∈ m * I :=
  (residueTensor_one_tmul_eq_zero316 m x).trans (relation_mem_smul_top316 m I x)

end PfaffianDescent
