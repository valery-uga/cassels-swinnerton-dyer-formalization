import PfaffianDescent.FlatKoszulCoordinates211

/-! Source candidate: the actual flat tensor Ext map transports the actual
local Serre class, with its coefficient mapped by the given ring homomorphism. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S]
variable [HasExt.{u + 1} (ModuleCat.{u} R)] [HasExt.{u + 1} (ModuleCat.{u} S)]

theorem flatKoszulSerreExtOne_transport211
    (φ : R →+* S) (hφ : φ.Flat) (f g c : R)
    (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hf' : φ f ∈ S⁰)
    (hg' : Ideal.Quotient.mk (Ideal.span {φ f}) (φ g) ∈ (S ⧸ Ideal.span {φ f})⁰) :
    (cubicPointTraceFieldBaseChangeLocalExtMap φ hφ _ _ 1
      (localSerreExtensionModuleComplex_shortExact f g c hf hg).extClass).comp
        (Ext.mk₀ (pointKoszulFlatBaseChangeFreeIso φ).hom) (add_zero 1) =
      (Ext.mk₀ (flatKoszulIdealIso211 φ hφ f g).hom).comp
        (localSerreExtensionModuleComplex_shortExact (φ f) (φ g) (φ c) hf' hg').extClass
        (zero_add 1) := by
  letI := cubicPointTraceFieldBaseChangeLocalScalarsPreservesFiniteLimits φ hφ
  let F := ModuleCat.extendScalars φ
  let hK := localKoszulIdealComplex_shortExact f g hf hg
  let hK' := localKoszulIdealComplex_shortExact (φ f) (φ g) hf' hg'
  have hn := (hK.map_of_exact F).extClass_naturality hK'
    (flatKoszulIdealComparison211 φ hφ f g)
  change (hK.map_of_exact F).extClass.comp
      (Ext.mk₀ (pointKoszulFlatBaseChangeFreeIso φ).hom) (add_zero 1) =
    (Ext.mk₀ (flatKoszulIdealIso211 φ hφ f g).hom).comp hK'.extClass (zero_add 1) at hn
  rw [← Ext.mapExactFunctor_extClass F hK] at hn
  change ((localSerreExtensionModuleComplex_shortExact f g c hf hg).extClass.mapExactFunctor F).comp
      (Ext.mk₀ (pointKoszulFlatBaseChangeFreeIso φ).hom) (add_zero 1) = _
  rw [localSerreExtClass_eq_koszul_boundary f g c hf hg,
    localSerreExtClass_eq_koszul_boundary (φ f) (φ g) (φ c) hf' hg',
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    flatKoszulCoefficient_square211,
    ← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    hn, Ext.comp_assoc_of_third_deg_zero]

theorem flatKoszulSerreExtTwo_transport211
    (φ : R →+* S) (hφ : φ.Flat) (f g c : R)
    (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hf' : φ f ∈ S⁰)
    (hg' : Ideal.Quotient.mk (Ideal.span {φ f}) (φ g) ∈ (S ⧸ Ideal.span {φ f})⁰) :
    (cubicPointTraceFieldBaseChangeLocalExtMap φ hφ _ _ 2
      (localSerreExtTwoClass f g c hf hg)).comp
        (Ext.mk₀ (pointKoszulFlatBaseChangeFreeIso φ).hom) (add_zero 2) =
      (Ext.mk₀ (pointKoszulFlatBaseChangePointIso φ f g).hom).comp
        (localSerreExtTwoClass (φ f) (φ g) (φ c) hf' hg') (zero_add 2) := by
  letI := cubicPointTraceFieldBaseChangeLocalScalarsPreservesFiniteLimits φ hφ
  let F := ModuleCat.extendScalars φ
  let hQ := localSerreIdealQuotientComplex_shortExact f g
  let hQ' := localSerreIdealQuotientComplex_shortExact (φ f) (φ g)
  have hn := (hQ.map_of_exact F).extClass_naturality hQ'
    (flatKoszulQuotientComparison211 φ hφ f g)
  change (hQ.map_of_exact F).extClass.comp
      (Ext.mk₀ (flatKoszulIdealIso211 φ hφ f g).hom) (add_zero 1) =
    (Ext.mk₀ (pointKoszulFlatBaseChangePointIso φ f g).hom).comp hQ'.extClass (zero_add 1) at hn
  rw [← Ext.mapExactFunctor_extClass F hQ] at hn
  have he := flatKoszulSerreExtOne_transport211 φ hφ f g c hf hg hf' hg'
  change ((localSerreExtensionModuleComplex_shortExact f g c hf hg).extClass.mapExactFunctor F).comp
      (Ext.mk₀ (pointKoszulFlatBaseChangeFreeIso φ).hom) (add_zero 1) = _ at he
  change ((localSerreExtTwoClass f g c hf hg).mapExactFunctor F).comp
    (Ext.mk₀ (pointKoszulFlatBaseChangeFreeIso φ).hom) (add_zero 2) = _
  unfold localSerreExtTwoClass
  rw [Ext.mapExactFunctor_comp, Ext.comp_assoc_of_third_deg_zero, he,
    ← Ext.comp_assoc_of_second_deg_zero, hn]
  exact Ext.comp_assoc _ _ _ (zero_add 1) rfl (by omega)

end PfaffianDescent
