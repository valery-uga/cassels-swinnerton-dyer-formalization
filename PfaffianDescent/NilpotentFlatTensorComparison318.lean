import PfaffianDescent.NilpotentRegularityBridge167
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
A nilpotent coefficient reduction detects bijectivity
of a module map when the target is flat over the coefficient ring. This
applies to A-linear maps after restricting scalars to an Artin base S;
neither source nor target need be finitely generated over S.
-/

noncomputable section
namespace AllCharacteristics
open Module LinearMap TensorProduct
universe u v w

/-- Vanishing after tensoring with a nilpotent quotient detects the zero
module, even for modules infinite over the coefficient ring. -/
theorem subsingleton_of_nilpotent_tensor_quotient318
    {R : Type u} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    {M : Type v} [AddCommGroup M] [Module R M]
    [Subsingleton ((R ⧸ I) ⊗[R] M)] : Subsingleton M := by
  have htop : (⊤ : Submodule R M) ≤ I • (⊤ : Submodule R M) := by
    intro x hx
    have hxzero : (1 : R ⧸ I) ⊗ₜ[R] x = 0 := Subsingleton.elim _ _
    have hquot : (Submodule.Quotient.mk x : M ⧸ I • (⊤ : Submodule R M)) = 0 := by
      simpa only [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] using
        congrArg (TensorProduct.quotTensorEquivQuotSMul M I) hxzero
    exact (Submodule.Quotient.mk_eq_zero _).mp hquot
  have hzeroTop : (⊤ : Submodule R M) ≤ ⊥ :=
    PfaffianDescent.submodule_le_of_nilpotent_smul_error167 I hI
      (⊤ : Submodule R M) ⊥ (by simpa only [bot_sup_eq] using htop)
  have hz : (⊤ : Submodule R M) = ⊥ := le_antisymm hzeroTop bot_le
  have hzero : ∀ x : M, x = 0 := by
    intro x
    have hx : x ∈ (⊤ : Submodule R M) := Submodule.mem_top
    rw [hz] at hx
    exact (Submodule.mem_bot R).mp hx
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

/-- Reduced surjectivity lifts across every nilpotent coefficient ideal. -/
theorem surjective_of_nilpotent_lTensor_surjective318
    {R : Type u} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    {F : Type v} {M : Type w} [AddCommGroup F] [AddCommGroup M]
    [Module R F] [Module R M] (f : F →ₗ[R] M)
    (hred : Function.Surjective (f.lTensor (R ⧸ I))) : Function.Surjective f := by
  have htop : (⊤ : Submodule R M) ≤ f.range ⊔ I • (⊤ : Submodule R M) := by
    intro m hm
    obtain ⟨t, ht⟩ := hred (1 ⊗ₜ[R] m)
    obtain ⟨n, hn⟩ := TensorProduct.mk_surjective
      (R := R) (M := F) (S := R ⧸ I) Ideal.Quotient.mk_surjective t
    have htn : (1 : R ⧸ I) ⊗ₜ[R] f n = 1 ⊗ₜ[R] m := by
      rw [← hn] at ht
      change (f.lTensor (R ⧸ I)) ((1 : R ⧸ I) ⊗ₜ[R] n) =
        (1 : R ⧸ I) ⊗ₜ[R] m at ht
      simpa only [LinearMap.lTensor_tmul] using ht
    have hq : (Submodule.Quotient.mk (f n) : M ⧸ I • (⊤ : Submodule R M)) =
        Submodule.Quotient.mk m := by
      simpa only [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul] using
        congrArg (TensorProduct.quotTensorEquivQuotSMul M I) htn
    have hdiff : m - f n ∈ I • (⊤ : Submodule R M) :=
      (Submodule.Quotient.eq _).mp hq.symm
    have hsum : f n + (m - f n) = m := by abel
    rw [← hsum]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self f n) hdiff
  have htotal : (⊤ : Submodule R M) ≤ f.range :=
    PfaffianDescent.submodule_le_of_nilpotent_smul_error167 I hI
      (⊤ : Submodule R M) f.range htop
  apply LinearMap.range_eq_top.mp
  exact le_antisymm le_top htotal

/-- Flatness of the TARGET gives exact kernel base change; nilpotence
then detects its vanishing. This is suitable for relative syzygy modules. -/
theorem bijective_of_nilpotent_lTensor_bijective_of_flat318
    {R : Type u} [CommRing R] (I : Ideal R) (hI : IsNilpotent I)
    {F : Type v} {M : Type w} [AddCommGroup F] [AddCommGroup M]
    [Module R F] [Module R M] [Module.Flat R M] (f : F →ₗ[R] M)
    (hred : Function.Bijective (f.lTensor (R ⧸ I))) : Function.Bijective f := by
  have hf := surjective_of_nilpotent_lTensor_surjective318 I hI f hred.surjective
  have hki : Function.Injective (f.ker.subtype.lTensor (R ⧸ I)) :=
    LinearMap.lTensor_injective_of_exact_of_flat f hf f.ker.subtype
      f.ker.subtype_injective (LinearMap.exact_subtype_ker_map f) (R ⧸ I)
  have hkzero : ∀ x : (R ⧸ I) ⊗[R] f.ker, x = 0 := by
    intro x
    apply hki
    apply hred.injective
    rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      (LinearMap.exact_subtype_ker_map f).linearMap_comp_eq_zero,
      LinearMap.lTensor_zero, LinearMap.zero_apply]
  letI : Subsingleton ((R ⧸ I) ⊗[R] f.ker) :=
    ⟨fun x y => (hkzero x).trans (hkzero y).symm⟩
  letI : Subsingleton f.ker := subsingleton_of_nilpotent_tensor_quotient318 I hI
  refine ⟨?_, hf⟩
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.eq_bot_of_subsingleton

end AllCharacteristics
end
