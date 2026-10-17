import PfaffianDescent.CubicClosedPointSerreLocalFreeAlgebra

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors
universe u w
variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- Freeness of the actual middle module makes its relation coefficient a unit.
The constructed exact-sequence comparisons identify the actual Yoneda product
with that nonzero residue coefficient. -/
theorem cubicClosedPointSerreLocalFree_yoneda_nonzero_of_free
    [HasExt.{w} (ModuleCat.{u} R)]
    (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    (N E : ModuleCat.{u} R) [Module.Free R E] (ι₀ : N ⟶ E) (π₀ : E ⟶ T.X₁)
    (hzero : ι₀ ≫ π₀ = 0)
    (hS : (ShortComplex.mk ι₀ π₀ hzero).ShortExact)
    (f g : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hspan : Ideal.span ({f, g} : Set R) = IsLocalRing.maximalIdeal R)
    (e₂ : T.X₂ ≅ ModuleCat.of R R)
    (e₃ : T.X₃ ≅ ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)))
    (eN : N ≅ ModuleCat.of R R) :
    hT.extClass.comp hS.extClass (show 1 + 1 = 2 by omega) ≠ 0 := by
  obtain ⟨e₂', hsquare⟩ :=
    cubicClosedPointSerreLocalFree_normalize_quotient T hT f g hspan e₂ e₃
  let eI := cubicClosedPointSerreLocalFree_idealIso T hT f g e₂' e₃ hsquare
  let aT := cubicClosedPointSerreLocalFree_idealSequenceIso T hT f g e₂' e₃ hsquare
  let ι : R →ₗ[R] E := ι₀.hom.comp eN.inv.hom
  let π : E →ₗ[R] Ideal.span ({f, g} : Set R) := eI.hom.hom.comp π₀.hom
  have hraw : Function.Exact ι₀ π₀ :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact
  have hexact : Function.Exact ι π := by
    have hpre : Function.Exact (ι₀ ∘ eN.inv) π₀ :=
      functionExact_precomp_of_surjective ι₀ eN.inv π₀ hraw
        eN.symm.toLinearEquiv.surjective
    exact hpre.comp_injective eI.hom eI.toLinearEquiv.injective (map_zero _)
  have hinj : Function.Injective ι :=
    ((ModuleCat.mono_iff_injective ι₀).mp hS.mono_f).comp
      eN.symm.toLinearEquiv.injective
  have hsurj : Function.Surjective π :=
    eI.toLinearEquiv.surjective.comp ((ModuleCat.epi_iff_surjective π₀).mp hS.epi_g)
  obtain ⟨e₁, he₁⟩ := hsurj ⟨f, Ideal.subset_span (by simp)⟩
  obtain ⟨e₂₀, he₂₀⟩ := hsurj ⟨g, Ideal.subset_span (by simp)⟩
  have hrelzero : π ((-g) • e₁ + f • e₂₀) = 0 := by
    rw [map_add, map_smul, map_smul, he₁, he₂₀]
    apply Subtype.ext
    change -g * f + f * g = 0
    ring
  obtain ⟨c, hc⟩ := (hexact _).mp hrelzero
  have hrel : (-g) • e₁ + f • e₂₀ = c • ι 1 := by
    rw [← hc]
    simpa only [smul_eq_mul, mul_one] using ι.map_smul c (1 : R)
  let q := localSerreExtensionPresentationEquiv_of_exact_of_lifts
    ι f g c π e₁ e₂₀ hexact hinj he₁ he₂₀ hrel hf hg
  let aS : ShortComplex.mk ι₀ π₀ hzero ⟶ localSerreExtensionModuleComplex f g c :=
    ShortComplex.homMk eN.hom q.toModuleIso.hom eI.hom (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro n
      change localSerreExtensionFromRing f g c (eN.hom n) = q (ι₀ n)
      have h := localSerreExtensionPresentationEquiv_of_exact_of_lifts_inclusion
        ι f g c π e₁ e₂₀ hexact hinj he₁ he₂₀ hrel hf hg (eN.hom n)
      have hi : ι (eN.hom n) = ι₀ n := by
        change ι₀ (eN.inv (eN.hom n)) = ι₀ n
        rw [eN.hom_inv_id_apply]
      rw [hi] at h
      exact h.symm) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro e
      exact localSerreExtensionPresentationEquiv_of_exact_of_lifts_projection
        ι f g c π e₁ e₂₀ hexact hinj he₁ he₂₀ hrel hf hg e)
  have halpha := ShortComplex.ShortExact.extClass_naturality hT
    (localSerreIdealQuotientComplex_shortExact f g) aT.hom
  have hbeta := ShortComplex.ShortExact.extClass_naturality hS
    (localSerreExtensionModuleComplex_shortExact f g c hf hg) aS
  have htransport : (Ext.mk₀ e₃.inv).comp
      ((hT.extClass.comp hS.extClass (show 1 + 1 = 2 by omega)).comp
        (Ext.mk₀ eN.hom) (add_zero 2)) (zero_add 2) =
      localSerreExtTwoClass f g c hf hg := by
    exact ext_comp_transport_of_common_middle e₃ eN eI.hom hT.extClass hS.extClass
      (localSerreIdealQuotientComplex_shortExact f g).extClass
      (localSerreExtensionModuleComplex_shortExact f g c hf hg).extClass halpha hbeta
  letI : Module.Free R (localSerreExtensionPresentation f g c) := Module.Free.of_equiv q
  have hfm : f ∈ IsLocalRing.maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  have hgm : g ∈ IsLocalRing.maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  have hcunit : IsUnit c :=
    (localSerreExtensionPresentation_free_iff_isUnit f g c hf hfm hgm).mp inferInstance
  have hclass : localSerreExtTwoClass f g c hf hg ≠ 0 := by
    intro hz
    have hquot := congrArg (localExtTwoCoefficientEquiv f g hf hg).symm hz
    rw [localExtTwoCoefficientEquiv_symm_localSerreExtTwoClass, map_zero] at hquot
    have hcm := Ideal.Quotient.eq_zero_iff_mem.mp hquot
    rw [hspan] at hcm
    exact (IsLocalRing.notMem_maximalIdeal.mpr hcunit) hcm
  intro hz
  apply hclass
  rw [hz, Ext.zero_comp, Ext.comp_zero] at htransport
  exact htransport.symm

end PfaffianDescent
