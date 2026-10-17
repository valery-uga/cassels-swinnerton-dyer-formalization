import PfaffianDescent.LocalExtResidueInjective
import PfaffianDescent.PointCartierNativeStalkPrincipalNormalization
import PfaffianDescent.VoisinSheafStalk
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Normalizing the actual local ideal sequence at a closed field point

An arbitrary rank-one coordinate on the middle term need not identify its
quotient map with the standard quotient map. Surjectivity constructs the
unit correction. Kernel universality then constructs the ideal endpoint and
both squares of the actual short exact sequence.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open scoped nonZeroDivisors
universe u w

variable {R : Type u} [CommRing R] [IsLocalRing R]

theorem cubicClosedPointSerreLocalFree_normalize_quotient
    (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    (f g : R) (hspan : Ideal.span ({f, g} : Set R) = IsLocalRing.maximalIdeal R)
    (e₂ : T.X₂ ≅ ModuleCat.of R R)
    (e₃ : T.X₃ ≅ ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R))) :
    ∃ e₂' : T.X₂ ≅ ModuleCat.of R R,
      T.g ≫ e₃.hom = e₂'.hom ≫ (localSerreIdealQuotientComplex f g).g := by
  let v : ModuleCat.of R R ⟶ ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)) :=
    e₂.inv ≫ T.g ≫ e₃.hom
  have hsurj : Function.Surjective v := by
    haveI : Epi T.g := hT.epi_g
    haveI : Epi v := by dsimp [v]; infer_instance
    exact (ModuleCat.epi_iff_surjective v).mp inferInstance
  have hv : ∀ r : R, v r = r • v 1 := by
    intro r
    simpa only [smul_eq_mul, mul_one] using v.hom.map_smul r (1 : R)
  have hne : v 1 ≠ 0 := by
    intro hzero
    obtain ⟨r, hr⟩ := hsurj 1
    have hone : (1 : R ⧸ IsLocalRing.maximalIdeal R) = 0 := by
      have h := (hv r).trans (by rw [hzero, smul_zero])
      rw [hr] at h
      change (1 : R ⧸ Ideal.span ({f, g} : Set R)) = 0 at h
      rw [hspan] at h
      exact h
    exact one_ne_zero hone
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (v 1)
  have haunit : IsUnit a := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit a).mp
    intro hazero
    apply hne
    rw [← ha]
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R) a = 0 at hazero
    rw [hspan]
    exact hazero
  let e₂' := e₂ ≪≫ (LinearEquiv.smulOfUnit haunit.unit : R ≃ₗ[R] R).toModuleIso
  refine ⟨e₂', ?_⟩
  rw [← cancel_epi e₂.inv]
  have he₂' : e₂.inv ≫ e₂'.hom =
      (LinearEquiv.smulOfUnit haunit.unit : R ≃ₗ[R] R).toModuleIso.hom := by
    simp only [e₂', Iso.trans_hom, e₂.inv_hom_id_assoc]
  change e₂.inv ≫ T.g ≫ e₃.hom =
    e₂.inv ≫ e₂'.hom ≫ ModuleCat.ofHom (Ideal.span ({f, g} : Set R)).mkQ
  rw [← Category.assoc e₂.inv e₂'.hom, he₂']
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change v r = Ideal.Quotient.mk (Ideal.span ({f, g} : Set R))
    ((haunit.unit : R) * r)
  rw [hv, ← ha, haunit.unit_spec]
  simpa [Ideal.Quotient.mkₐ, smul_eq_mul, mul_comm] using
    ((Ideal.Quotient.mkₐ R (Ideal.span ({f, g} : Set R))).toLinearMap.map_smul r a).symm

def cubicClosedPointSerreLocalFree_idealIso
    (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact) (f g : R)
    (e₂ : T.X₂ ≅ ModuleCat.of R R)
    (e₃ : T.X₃ ≅ ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)))
    (hsquare : T.g ≫ e₃.hom = e₂.hom ≫ (localSerreIdealQuotientComplex f g).g) :
    T.X₁ ≅ ModuleCat.of R (Ideal.span ({f, g} : Set R)) :=
  KernelFork.mapIsoOfIsLimit hT.fIsKernel
    (localSerreIdealQuotientComplex_shortExact f g).fIsKernel
    (Arrow.isoMk e₂ e₃ hsquare.symm)

theorem cubicClosedPointSerreLocalFree_idealIso_square
    (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact) (f g : R)
    (e₂ : T.X₂ ≅ ModuleCat.of R R)
    (e₃ : T.X₃ ≅ ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)))
    (hsquare : T.g ≫ e₃.hom = e₂.hom ≫ (localSerreIdealQuotientComplex f g).g) :
    T.f ≫ e₂.hom = (cubicClosedPointSerreLocalFree_idealIso T hT f g e₂ e₃ hsquare).hom ≫
      (localSerreIdealQuotientComplex f g).f := by
  exact (KernelFork.mapOfIsLimit_ι (KernelFork.ofι T.f T.zero)
    (localSerreIdealQuotientComplex_shortExact f g).fIsKernel
    (Arrow.isoMk e₂ e₃ hsquare.symm).hom).symm

def cubicClosedPointSerreLocalFree_idealSequenceIso
    (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact) (f g : R)
    (e₂ : T.X₂ ≅ ModuleCat.of R R)
    (e₃ : T.X₃ ≅ ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)))
    (hsquare : T.g ≫ e₃.hom = e₂.hom ≫ (localSerreIdealQuotientComplex f g).g) :
    T ≅ localSerreIdealQuotientComplex f g :=
  ShortComplex.isoMk (cubicClosedPointSerreLocalFree_idealIso T hT f g e₂ e₃ hsquare)
    e₂ e₃ (cubicClosedPointSerreLocalFree_idealIso_square T hT f g e₂ e₃ hsquare).symm
    hsquare.symm

/-- The actual two-extension determines a unit relation coefficient, and
therefore free rank-two coordinates on its actual middle module. Every
comparison map used here is constructed from the exact sequences. -/
theorem cubicClosedPointSerreLocalFree_of_nonzero_yoneda
    [HasExt.{w} (ModuleCat.{u} R)]
    (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    (N E : ModuleCat.{u} R) (ι₀ : N ⟶ E) (π₀ : E ⟶ T.X₁)
    (hzero : ι₀ ≫ π₀ = 0)
    (hS : (ShortComplex.mk ι₀ π₀ hzero).ShortExact)
    (f g : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hspan : Ideal.span ({f, g} : Set R) = IsLocalRing.maximalIdeal R)
    (e₂ : T.X₂ ≅ ModuleCat.of R R)
    (e₃ : T.X₃ ≅ ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)))
    (eN : N ≅ ModuleCat.of R R)
    (hne : hT.extClass.comp hS.extClass (show 1 + 1 = 2 by omega) ≠ 0) :
    Nonempty (E ≃ₗ[R] R × R) := by
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
  have hclass : localSerreExtTwoClass f g c hf hg ≠ 0 := by
    intro hz
    apply hne
    let e := (extPostcompIsoOfIso.{w,u,u+1} (X := T.X₃) (n := 2) eN).trans
      (extPrecompIsoOfIso.{w,u,u+1} (Y := ModuleCat.of R R) (n := 2) e₃)
    apply e.injective
    change (Ext.mk₀ e₃.inv).comp
      ((hT.extClass.comp hS.extClass (show 1 + 1 = 2 by omega)).comp
        (Ext.mk₀ eN.hom) (add_zero 2)) (zero_add 2) = e 0
    rw [htransport, hz, map_zero]
  have hcunit : IsUnit c := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hcm
    apply hclass
    apply (localExtTwoCoefficientEquiv f g hf hg).symm.injective
    rw [localExtTwoCoefficientEquiv_symm_localSerreExtTwoClass, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hspan.symm ▸ hcm)
  have hrelunit : (-g) • e₁ + f • e₂₀ = (hcunit.unit : R) • ι 1 := by
    rw [hcunit.unit_spec]
    exact hrel
  obtain ⟨t, _⟩ := exists_freeCoordinates_of_exact_of_lifts_of_unit_coordinate
    ι f g π e₁ e₂₀ hexact hinj he₁ he₂₀ hcunit.unit hrelunit hf hg
  exact ⟨t⟩

/-- The free middle module supplies unit generator lifts in a normalization
of the actual ideal sequence. The two sequence squares are retained so
that this stalk data can be spread to an actual free neighborhood. -/
theorem cubicClosedPointSerreLocalFree_unit_lifts_of_free
    (T : ShortComplex (ModuleCat.{u} R)) (hT : T.ShortExact)
    (N E : ModuleCat.{u} R) [Module.Free R E]
    (ι₀ : N ⟶ E) (π₀ : E ⟶ T.X₁) (hzero : ι₀ ≫ π₀ = 0)
    (hS : (ShortComplex.mk ι₀ π₀ hzero).ShortExact)
    (f g : R) (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hspan : Ideal.span ({f, g} : Set R) = IsLocalRing.maximalIdeal R)
    (e₂ : T.X₂ ≅ ModuleCat.of R R)
    (e₃ : T.X₃ ≅ ModuleCat.of R (R ⧸ Ideal.span ({f, g} : Set R)))
    (eN : N ≅ ModuleCat.of R R) :
    ∃ (e₂' : T.X₂ ≅ ModuleCat.of R R)
      (eI : T.X₁ ≅ ModuleCat.of R (Ideal.span ({f, g} : Set R))),
      T.f ≫ e₂'.hom = eI.hom ≫ (localSerreIdealQuotientComplex f g).f ∧
      T.g ≫ e₃.hom = e₂'.hom ≫ (localSerreIdealQuotientComplex f g).g ∧
      ∃ (c : R) (e₁ e₂₀ : E), IsUnit c ∧
        eI.hom (π₀ e₁) = ⟨f, Ideal.subset_span (by simp)⟩ ∧
        eI.hom (π₀ e₂₀) = ⟨g, Ideal.subset_span (by simp)⟩ ∧
        (-g) • e₁ + f • e₂₀ = ι₀ (eN.inv c) ∧
        Nonempty (E ≃ₗ[R] localSerreExtensionPresentation f g c) := by
  obtain ⟨e₂', hsquare⟩ :=
    cubicClosedPointSerreLocalFree_normalize_quotient T hT f g hspan e₂ e₃
  let eI := cubicClosedPointSerreLocalFree_idealIso T hT f g e₂' e₃ hsquare
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
  letI : Module.Free R (localSerreExtensionPresentation f g c) := Module.Free.of_equiv q
  have hfm : f ∈ IsLocalRing.maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  have hgm : g ∈ IsLocalRing.maximalIdeal R := hspan ▸ Ideal.subset_span (by simp)
  have hcunit : IsUnit c :=
    (localSerreExtensionPresentation_free_iff_isUnit f g c hf hfm hgm).mp inferInstance
  refine ⟨e₂', eI, cubicClosedPointSerreLocalFree_idealIso_square T hT f g e₂' e₃ hsquare,
    hsquare, c, e₁, e₂₀, hcunit, he₁, he₂₀, ?_, ⟨q⟩⟩
  exact hc.symm

end PfaffianDescent
