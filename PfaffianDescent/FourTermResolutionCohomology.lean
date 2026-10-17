import PfaffianDescent.SchemeModuleCohomology
import PfaffianDescent.VoisinSerreTwistSectionInjection
import PfaffianDescent.SchemeModuleGlobalSections
import PfaffianDescent.SheafModuleEnoughInjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! SOURCE ONLY / UNVERIFIED. Split an actual four-term exact resolution at
its actual final kernel, and use the covariant Ext long exact sequences.
The generic vanishings here are discharged in the separate actual P3 leaf. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

-- Actual production errors show scheme/raw module category aliases obstruct inference.
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u

/-- Enough injectives and the actual small Hom types supply the infrastructure;
this is not a geometric or cohomological vanishing assumption. -/
theorem resolutionSchemeModules_hasExt (X : Scheme.{u}) : HasExt.{u} X.Modules := by
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  exact hasExt_of_enoughInjectives _

/-- Vanishing commutes with a finite biproduct in the SECOND Ext variable. -/
theorem resolution_ext_finite_biproduct_target_subsingleton
    {C : Type*} [Category C] [Abelian C] [HasExt.{u} C]
    {J : Type*} [Fintype J] (X : C) (Y : J → C) [HasBiproduct Y] (n : ℕ)
    [∀ j, Subsingleton (CategoryTheory.Abelian.Ext.{u} X (Y j) n)] :
    Subsingleton (CategoryTheory.Abelian.Ext.{u} X (⨁ Y) n) := by
  exact (CategoryTheory.Abelian.Ext.addEquivBiproduct X (biproduct.isBilimit Y) n).injective.subsingleton

/-- The actual morphism-valued global map of a short exact sequence.
Transfer from the existing sections LES using the genuine unit-Hom equivalence. -/
theorem resolution_shortExact_globalMap_bijective
    {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (base : X ⟶ Spec (.of K)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Subsingleton (schemeModuleCohomology X S.X₁ 0)]
    [Subsingleton (schemeModuleCohomology X S.X₁ 1)] :
    Function.Bijective (schemeModuleGlobalSectionsMap base S.g) := by
  -- Transfer the GIVEN same-universe HasExt proof to the underlying sheaf category,
  -- rather than searching for a new localization/smallness construction.
  let hExt : HasExt.{u} X.Modules := inferInstance
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  let Sraw : ShortComplex (SheafOfModules.{u} X.ringCatSheaf) := S
  have hSraw : Sraw.ShortExact := hS
  letI : Subsingleton Sraw.X₁.sections :=
    (schemeModuleCohomology_zero_subsingleton_iff_sections X S.X₁).mp inferInstance
  letI : Subsingleton (CategoryTheory.Abelian.Ext.{u}
      (SheafOfModules.unit X.ringCatSheaf) Sraw.X₁ 1) :=
    (inferInstance : Subsingleton (schemeModuleCohomology X S.X₁ 1))
  let M₂ : SheafOfModules.{u} X.ringCatSheaf := Sraw.X₂
  let M₃ : SheafOfModules.{u} X.ringCatSheaf := Sraw.X₃
  let gRaw : M₂ ⟶ M₃ := Sraw.g
  let e₂ : (SheafOfModules.unit X.ringCatSheaf ⟶ M₂) ≃ M₂.sections :=
    M₂.unitHomEquiv
  let e₃ : (SheafOfModules.unit X.ringCatSheaf ⟶ M₃) ≃ M₃.sections :=
    M₃.unitHomEquiv
  have hb : Function.Bijective (SheafOfModules.sectionsMap gRaw) :=
    sectionsMap_bijective_of_shortExact_of_left_h0_h1_vanish (X := X) Sraw hSraw
  have hcomp (s : SheafOfModules.unit X.ringCatSheaf ⟶ M₂) :
      e₃ (s ≫ gRaw) = SheafOfModules.sectionsMap gRaw (e₂ s) :=
    SheafOfModules.unitHomEquiv_comp_apply s gRaw
  change Function.Bijective
    (fun s : SheafOfModules.unit X.ringCatSheaf ⟶ M₂ => s ≫ gRaw)
  constructor
  · intro s t h
    apply e₂.injective
    apply hb.1
    calc
      SheafOfModules.sectionsMap gRaw (e₂ s) = e₃ (s ≫ gRaw) := (hcomp s).symm
      _ = e₃ (t ≫ gRaw) := congrArg e₃ h
      _ = SheafOfModules.sectionsMap gRaw (e₂ t) := hcomp t
  · intro t
    obtain ⟨s, hs⟩ := hb.2 (e₃ t)
    refine ⟨e₂.symm s, ?_⟩
    apply e₃.injective
    calc
      e₃ (e₂.symm s ≫ gRaw) =
          SheafOfModules.sectionsMap gRaw (e₂ (e₂.symm s)) := hcomp (e₂.symm s)
      _ = SheafOfModules.sectionsMap gRaw s :=
        congrArg (SheafOfModules.sectionsMap gRaw) (e₂.apply_symm_apply s)
      _ = e₃ t := hs

/-- The genuine long-exact-cohomology argument for 0→A→B→C→D→0.
Neither an image/kernel comparison nor an auxiliary short exact sequence is
supplied: both short exact sequences are constructed from the SAME f,g,h. -/
theorem resolution_fourTerm_globalMap_bijective
    {K : Type u} [Field K] {X : Scheme.{u}} [HasExt.{u} X.Modules]
    (base : X ⟶ Spec (.of K)) {A B C D : X.Modules}
    (f : A ⟶ B) (g : B ⟶ C) (h : C ⟶ D)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0)
    (hleft : (ShortComplex.mk f g hfg).Exact)
    (hright : (ShortComplex.mk g h hgh).Exact)
    [Mono f] [Epi h]
    [Subsingleton (schemeModuleCohomology X A 1)]
    [Subsingleton (schemeModuleCohomology X A 2)]
    [Subsingleton (schemeModuleCohomology X B 0)]
    [Subsingleton (schemeModuleCohomology X B 1)] :
    Function.Bijective (schemeModuleGlobalSectionsMap base h) := by
  let q : B ⟶ kernel h := kernel.lift h g hgh
  have hfq : f ≫ q = 0 := by
    apply (cancel_mono (kernel.ι h)).mp
    simp only [Category.assoc, q, kernel.lift_ι, hfg, zero_comp]
  let L : ShortComplex X.Modules := ShortComplex.mk f q hfq
  let φ : L ⟶ ShortComplex.mk f g hfg :=
    { τ₁ := 𝟙 A
      τ₂ := 𝟙 B
      τ₃ := kernel.ι h
      comm₁₂ := by simp [L]
      comm₂₃ := by simp [L, q] }
  letI : Epi q := hright.epi_kernelLift
  have hL : L.ShortExact :=
    ShortComplex.ShortExact.mk'
      ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hleft)
      inferInstance inferInstance
  let R : ShortComplex X.Modules := ShortComplex.kernelSequence h
  letI : Mono R.f := by
    change Mono (kernel.ι h)
    infer_instance
  letI : Epi R.g := by
    change Epi h
    infer_instance
  have hR : R.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact h)
      inferInstance inferInstance
  letI : Subsingleton (schemeModuleCohomology X (kernel h) 0) :=
    schemeModuleCohomology_subsingleton_of_middle_and_next_left X L hL 0
  letI : Subsingleton (schemeModuleCohomology X (kernel h) 1) :=
    schemeModuleCohomology_subsingleton_of_middle_and_next_left X L hL 1
  letI : Subsingleton (schemeModuleCohomology X R.X₁ 0) :=
    (inferInstance : Subsingleton (schemeModuleCohomology X (kernel h) 0))
  letI : Subsingleton (schemeModuleCohomology X R.X₁ 1) :=
    (inferInstance : Subsingleton (schemeModuleCohomology X (kernel h) 1))
  change Function.Bijective (schemeModuleGlobalSectionsMap base R.g)
  exact resolution_shortExact_globalMap_bijective base R hR

end PfaffianDescent
