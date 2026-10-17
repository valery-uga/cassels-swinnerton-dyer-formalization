import PfaffianDescent.CorayOriginalChartGenericCompatibility
import PfaffianDescent.CorayBoundedOriginalEvaluationImage
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false

/-- Bounded ordinary equality transport for appLE with its actual
map-dependent containment proofs. -/
private theorem schemeHom_appLE_eq_of_eq001
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  cases h
  rfl

/-- On the literal open chart of the WHOLE full scheme image of a field
point, the actual section map to the field is injective and the actual
chart section map is surjective. Their composition is the ORIGINAL chart
hom. No image chart, quotient, map-factor or kernel outcome is supplied. -/
theorem fieldPoint_wholeImage_openChart_exists_literalSectionMaps001
    {R F : Type u} [CommRing R] [Field F] (X : Scheme.{u})
    (j : Spec (.of R) ⟶ X) [IsOpenImmersion j] (g : R →+* F)
    [QuasiCompact (Spec.map (CommRingCat.ofHom g) ≫ j)] :
    let f := Spec.map (CommRingCat.ofHom g) ≫ j
    let U := f.imageι ⁻¹ᵁ j.opensRange
    let e := (Scheme.ΓSpecIso (.of R)).symm ≪≫ IsOpenImmersion.ΓIsoTop j
    let beta : R →+* Γ(f.image, U) := (f.imageι.app j.opensRange).hom.comp e.hom.hom
    ∃ gamma : Γ(f.image, U) →+* F,
      Function.Injective gamma ∧ Function.Surjective beta ∧ gamma.comp beta = g := by
  classical
  let f := Spec.map (CommRingCat.ofHom g) ≫ j
  let C := f.ker.subscheme
  let i : C ⟶ X := f.ker.subschemeι
  let t : Spec (.of F) ⟶ C := f.toImage
  let V := j.opensRange
  let U := i ⁻¹ᵁ V
  let e := (Scheme.ΓSpecIso (.of R)).symm ≪≫ IsOpenImmersion.ΓIsoTop j
  let beta : R →+* Γ(C, U) := (i.app V).hom.comp e.hom.hom
  have ht : t ≫ i = f := Scheme.Hom.toImage_imageι f
  let hJ : (⊤ : (Spec (.of R)).Opens) ≤ j ⁻¹ᵁ V := by
    intro z _
    exact ⟨z, rfl⟩
  let hF : (⊤ : (Spec (.of F)).Opens) ≤ f ⁻¹ᵁ V := by
    intro z _
    exact ⟨Spec.map (CommRingCat.ofHom g) z, rfl⟩
  let hT : (⊤ : (Spec (.of F)).Opens) ≤ t ⁻¹ᵁ U := by
    intro z _
    change i (t z) ∈ V
    have hz := congrArg (fun h : Spec (.of F) ⟶ X => h z) ht
    change i (t z) = f z at hz
    rw [hz]
    exact hF (Set.mem_univ z)
  have hTtop : t ⁻¹ᵁ U = ⊤ := le_antisymm le_top hT
  let r := t.appLE U ⊤ hT
  let delta := (Spec (.of F)).presheaf.map (homOfLE hT).op
  letI : IsIso delta := by
    have hArrow : homOfLE hT = eqToHom hTtop.symm := Subsingleton.elim _ _
    dsimp only [delta]
    rw [hArrow]
    infer_instance
  have hr : Function.Injective r.hom :=
    (ConcreteCategory.bijective_of_isIso delta).1.comp
      (f.toImage_app_injective ⟨V, isAffineOpen_opensRange j⟩)
  let gamma : Γ(C, U) →+* F := (Scheme.ΓSpecIso (.of F)).hom.hom.comp r.hom
  have hGamma : Function.Injective gamma :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of F)).hom).1.comp hr
  have hI : Function.Surjective (i.app V) :=
    f.ker.subschemeι_app_surjective ⟨V, isAffineOpen_opensRange j⟩
  have hBeta : Function.Surjective beta :=
    hI.comp (ConcreteCategory.bijective_of_isIso e.hom).2
  let hTi : (⊤ : (Spec (.of F)).Opens) ≤ (t ≫ i) ⁻¹ᵁ V := by
    change (⊤ : (Spec (.of F)).Opens) ≤ t ⁻¹ᵁ U
    exact hT
  have hComp : i.app V ≫ r = f.appLE V ⊤ hF := by
    calc
      _ = (t ≫ i).appLE V ⊤ hTi :=
        (Scheme.Hom.comp_appLE t i V ⊤ hTi).symm
      _ = f.appLE V ⊤ hF := schemeHom_appLE_eq_of_eq001 ht V ⊤ hTi hF
  have hJInv : e.inv = j.appLE V ⊤ hJ ≫ (Scheme.ΓSpecIso (.of R)).hom := by
    dsimp only [e]
    rw [Iso.trans_inv, Iso.symm_inv, affineChartSectionIso_inv_appLE]
  let hG : (⊤ : (Spec (.of F)).Opens) ≤
      (Spec.map (CommRingCat.ofHom g)) ⁻¹ᵁ (⊤ : (Spec (.of R)).Opens) := by simp
  have hGTop : (Spec.map (CommRingCat.ofHom g)).appLE ⊤ ⊤ hG =
      (Spec.map (CommRingCat.ofHom g)).appTop := by
    change (Spec.map (CommRingCat.ofHom g)).appTop ≫ (Spec (.of F)).presheaf.map
      (𝟙 (⊤ : (Spec (.of F)).Opens)).op = _
    simp
  have hFComp : j.appLE V ⊤ hJ ≫ (Spec.map (CommRingCat.ofHom g)).appTop = f.appLE V ⊤ hF := by
    rw [← hGTop]
    exact Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom g)) j V ⊤ ⊤ hJ hG
  have hSquare : e.hom ≫ i.app V ≫ r ≫ (Scheme.ΓSpecIso (.of F)).hom = CommRingCat.ofHom g := by
    rw [← Category.assoc (i.app V) r (Scheme.ΓSpecIso (.of F)).hom, hComp,
      ← hFComp, Category.assoc, Scheme.ΓSpecIso_naturality]
    rw [← Category.assoc (j.appLE V ⊤ hJ) (Scheme.ΓSpecIso (.of R)).hom (CommRingCat.ofHom g),
      ← hJInv, Iso.hom_inv_id_assoc]
  have hRingSquare : gamma.comp beta = g := by
    exact congrArg (fun h : CommRingCat.of R ⟶ CommRingCat.of F => h.hom) hSquare
  exact ⟨gamma, hGamma, hBeta, hRingSquare⟩

/-- The actual open of the SAME WHOLE full image has the literal full
chart kernel quotient ring, derived from actual section maps. -/
theorem fieldPoint_wholeImage_openChart_fullKernelQuotientIso001
    {R F : Type u} [CommRing R] [Field F] (X : Scheme.{u})
    (j : Spec (.of R) ⟶ X) [IsOpenImmersion j] (g : R →+* F)
    [QuasiCompact (Spec.map (CommRingCat.ofHom g) ≫ j)] :
    let f := Spec.map (CommRingCat.ofHom g) ≫ j
    Nonempty (Γ(f.image, f.imageι ⁻¹ᵁ j.opensRange) ≃+* (R ⧸ RingHom.ker g)) := by
  obtain ⟨gamma, hGamma, hBeta, hSquare⟩ :=
    fieldPoint_wholeImage_openChart_exists_literalSectionMaps001 X j g
  let f := Spec.map (CommRingCat.ofHom g) ≫ j
  let U := f.imageι ⁻¹ᵁ j.opensRange
  let e := (Scheme.ΓSpecIso (.of R)).symm ≪≫ IsOpenImmersion.ΓIsoTop j
  let beta : R →+* Γ(f.image, U) := (f.imageι.app j.opensRange).hom.comp e.hom.hom
  have hKernel : RingHom.ker beta = RingHom.ker g := by
    rw [← hSquare]
    exact (RingHom.ker_comp_of_injective beta hGamma).symm
  exact ⟨(beta.quotientKerEquivOfSurjective hBeta).symm.trans (Ideal.quotEquivOfEq hKernel)⟩

end PfaffianDescent.Coray
