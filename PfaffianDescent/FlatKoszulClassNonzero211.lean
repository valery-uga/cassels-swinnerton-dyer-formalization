import PfaffianDescent.FlatKoszulClassTransport211

/-! Source candidate: a genuine unit local coefficient remains nonzero
after the actual flat tensor Ext map, when the image ideal is proper. -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
variable {R S : Type u} [CommRing R] [CommRing S]

theorem localSerreExtTwoClass_unit_ne_zero211
    [HasExt.{u + 1} (ModuleCat.{u} R)] (f g c : R)
    (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hc : IsUnit c) (hproper : (1 : R) ∉ Ideal.span ({f, g} : Set R)) :
    localSerreExtTwoClass f g c hf hg ≠ 0 := by
  intro hz
  have hquot : Ideal.Quotient.mk (Ideal.span ({f, g} : Set R)) c = 0 := by
    rw [← localExtTwoCoefficientEquiv_symm_localSerreExtTwoClass f g c hf hg, hz, map_zero]
  have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hquot
  rcases hc with ⟨v, rfl⟩
  apply hproper
  have h := (Ideal.span ({f, g} : Set R)).mul_mem_left (↑v⁻¹ : R) hmem
  simpa using h

theorem flatKoszulSerreExtTwo_unit_ne_zero211
    [HasExt.{u + 1} (ModuleCat.{u} R)] [HasExt.{u + 1} (ModuleCat.{u} S)]
    (φ : R →+* S) (hφ : φ.Flat) (f g c : R)
    (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hf' : φ f ∈ S⁰)
    (hg' : Ideal.Quotient.mk (Ideal.span {φ f}) (φ g) ∈ (S ⧸ Ideal.span {φ f})⁰)
    (hc : IsUnit c) (hproper : (1 : S) ∉ Ideal.span ({φ f, φ g} : Set S)) :
    cubicPointTraceFieldBaseChangeLocalExtMap φ hφ _ _ 2
      (localSerreExtTwoClass f g c hf hg) ≠ 0 := by
  intro hz
  let e := pointKoszulFlatBaseChangePointIso φ f g
  let z := localSerreExtTwoClass (φ f) (φ g) (φ c) hf' hg'
  have ht := flatKoszulSerreExtTwo_transport211 φ hφ f g c hf hg hf' hg'
  have hzero : (Ext.mk₀ e.hom).comp z (zero_add 2) = 0 := by
    rw [← ht, hz, Ext.zero_comp]
  have hzero' := congrArg (fun w => (Ext.mk₀ e.inv).comp w (zero_add 2)) hzero
  have hz' : z = 0 := by
    simpa only [Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id, Ext.mk₀_id_comp,
      Ext.comp_zero] using hzero'
  exact localSerreExtTwoClass_unit_ne_zero211 (φ f) (φ g) (φ c) hf' hg'
    (hc.map φ) hproper hz'

end PfaffianDescent
