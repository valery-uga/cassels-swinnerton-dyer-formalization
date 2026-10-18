import PfaffianDescent.NilpotentFlatTensorComparison318
import Mathlib.LinearAlgebra.Isomorphisms

/-!
Actual kernel reduction from a commuting square. Neither a kernel comparison
isomorphism nor its compatibility with the square is a hypothesis.
-/

noncomputable section
namespace AllCharacteristics
open LinearMap TensorProduct
universe u v w v₀ w₀

/-- The canonical tensor comparison attached to a surjective reduction whose
kernel is precisely the coefficient ideal times the whole module. -/
def exactReductionTensorEquiv318
    {S : Type u} [CommRing S] (I : Ideal S)
    {M : Type v} {M₀ : Type w} [AddCommGroup M] [AddCommGroup M₀]
    [Module S M] [Module S M₀]
    (ρ : M →ₗ[S] M₀) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = I • (⊤ : Submodule S M)) :
    (S ⧸ I) ⊗[S] M ≃ₗ[S] M₀ :=
  TensorProduct.quotTensorEquivQuotSMul M I ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ
    ρ.quotKerEquivOfSurjective hρ

@[simp] theorem exactReductionTensorEquiv318_one_tmul
    {S : Type u} [CommRing S] (I : Ideal S)
    {M : Type v} {M₀ : Type w} [AddCommGroup M] [AddCommGroup M₀]
    [Module S M] [Module S M₀]
    (ρ : M →ₗ[S] M₀) (hρ : Function.Surjective ρ)
    (hker : ρ.ker = I • (⊤ : Submodule S M)) (x : M) :
    exactReductionTensorEquiv318 I ρ hρ hker ((1 : S ⧸ I) ⊗ₜ[S] x) = ρ x := by
  simp [exactReductionTensorEquiv318]

/-- Compatibility of the canonical comparisons is derived on pure tensors.
In particular, bijectivity of the reduced map detects bijectivity upstairs
when the target is coefficient-flat. -/
theorem bijective_of_exact_reduction_square318
    {S : Type u} [CommRing S] (I : Ideal S) (hI : IsNilpotent I)
    {F : Type v} {K : Type w} {F₀ : Type v₀} {K₀ : Type w₀}
    [AddCommGroup F] [AddCommGroup K] [AddCommGroup F₀] [AddCommGroup K₀]
    [Module S F] [Module S K] [Module S F₀] [Module S K₀]
    [Module.Flat S K]
    (f : F →ₗ[S] K) (f₀ : F₀ →ₗ[S] K₀)
    (ρF : F →ₗ[S] F₀) (hρF : Function.Surjective ρF)
    (hkerF : ρF.ker = I • (⊤ : Submodule S F))
    (ρK : K →ₗ[S] K₀) (hρK : Function.Surjective ρK)
    (hkerK : ρK.ker = I • (⊤ : Submodule S K))
    (hcomm : ∀ x, ρK (f x) = f₀ (ρF x))
    (hf₀ : Function.Bijective f₀) : Function.Bijective f := by
  let eF := exactReductionTensorEquiv318 I ρF hρF hkerF
  let eK := exactReductionTensorEquiv318 I ρK hρK hkerK
  have hsquare : eK.toLinearMap.comp (f.lTensor (S ⧸ I)) =
      f₀.comp eF.toLinearMap := by
    apply LinearMap.ext
    intro t
    obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective
      (R := S) (S := S ⧸ I) (M := F) Ideal.Quotient.mk_surjective t
    change eK ((f.lTensor (S ⧸ I)) ((1 : S ⧸ I) ⊗ₜ[S] x)) =
      f₀ (eF ((1 : S ⧸ I) ⊗ₜ[S] x))
    rw [LinearMap.lTensor_tmul]
    simp only [eF, eK, exactReductionTensorEquiv318_one_tmul]
    exact hcomm x
  have hred : Function.Bijective (f.lTensor (S ⧸ I)) := by
    have he : Function.Bijective
        (eK.symm.toLinearMap.comp (f₀.comp eF.toLinearMap)) :=
      eK.symm.bijective.comp (hf₀.comp eF.bijective)
    have heq : eK.symm.toLinearMap.comp (f₀.comp eF.toLinearMap) =
        f.lTensor (S ⧸ I) := by
      rw [← hsquare]
      ext x
      exact eK.symm_apply_apply _
    rwa [heq] at he
  exact bijective_of_nilpotent_lTensor_bijective_of_flat318 I hI f hred

/-- Kernel comparison in an exact reduction square. Flatness of G gives
K∩IF=IK; the proof also constructs lifts of every residue relation. -/
theorem exists_kernel_reduction_of_exact_square318
    {S : Type u} [CommRing S] (I : Ideal S)
    {F : Type v} {G : Type w} {F₀ : Type v₀} {G₀ : Type w₀}
    [AddCommGroup F] [AddCommGroup G] [AddCommGroup F₀] [AddCommGroup G₀]
    [Module S F] [Module S G] [Module S F₀] [Module S G₀]
    [Module.Flat S G]
    (f : F →ₗ[S] G) (hf : Function.Surjective f)
    (f₀ : F₀ →ₗ[S] G₀)
    (ρF : F →ₗ[S] F₀) (hρF : Function.Surjective ρF)
    (hkerF : ρF.ker = I • (⊤ : Submodule S F))
    (ρG : G →ₗ[S] G₀)
    (hkerG : ρG.ker = I • (⊤ : Submodule S G))
    (hcomm : ∀ x, ρG (f x) = f₀ (ρF x)) :
    ∃ ρK : f.ker →ₗ[S] f₀.ker,
      (∀ k, (ρK k : F₀) = ρF (k : F)) ∧
      Function.Surjective ρK ∧
      ρK.ker = I • (⊤ : Submodule S f.ker) := by
  let ρK : f.ker →ₗ[S] f₀.ker :=
    (ρF.comp f.ker.subtype).codRestrict f₀.ker (fun k => by
      change f₀ (ρF (k : F)) = 0
      rw [← hcomm, LinearMap.mem_ker.mp k.property, map_zero])
  refine ⟨ρK, fun _ => rfl, ?_, ?_⟩
  · intro k₀
    obtain ⟨x, hx⟩ := hρF (k₀ : F₀)
    have hfx : f x ∈ I • (⊤ : Submodule S G) := by
      rw [← hkerG]
      change ρG (f x) = 0
      rw [hcomm, hx]
      exact LinearMap.mem_ker.mp k₀.property
    have hmap : (I • (⊤ : Submodule S F)).map f =
        I • (⊤ : Submodule S G) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hf]
    obtain ⟨y, hy, hfy⟩ := Submodule.mem_map.mp (hmap.symm ▸ hfx)
    have hyzero : ρF y = 0 := by
      apply LinearMap.mem_ker.mp
      rwa [hkerF]
    have hxy : x - y ∈ f.ker := by
      change f (x - y) = 0
      rw [map_sub, hfy, sub_self]
    refine ⟨⟨x - y, hxy⟩, ?_⟩
    apply Subtype.ext
    change ρF (x - y) = (k₀ : F₀)
    rw [map_sub, hyzero, sub_zero, hx]
  · have hinter := LinearMap.ker_inf_smul_top_eq_smul_of_flat I f hf
    ext k
    change ρK k = 0 ↔ k ∈ I • (⊤ : Submodule S f.ker)
    rw [Submodule.mem_smul_top_iff, ← hinter]
    change ρK k = 0 ↔ (k : F) ∈ f.ker ∧ (k : F) ∈ I • (⊤ : Submodule S F)
    rw [← hkerF]
    constructor
    · intro hk
      refine ⟨k.property, ?_⟩
      exact congrArg Subtype.val hk
    · rintro ⟨_, hk⟩
      exact Subtype.ext hk

end AllCharacteristics
end
