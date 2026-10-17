import PfaffianDescent.VoisinSectionRepresenterCechHomExact
import PfaffianDescent.SectionRepresenterCechAugmentationExact
import PfaffianDescent.SectionRepresenterCechLocalExact
import PfaffianDescent.CechExtVanishingLowDegree
import PfaffianDescent.SectionRepresenterTop

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry MvPolynomial Opposite
open scoped BigOperators
namespace PfaffianDescent.ProjectiveNegativeTwist

universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/- The global low-degree Ext vanishing obtained from the standard affine cover.
The section-representer resolution is used as the source resolution, while the
concrete negative-twist Cech complex supplies exactness after Hom. -/
theorem p3_sectionRepresenter_ext_one_and_two_subsingleton
    [HasExt.{u} (Proj PS).Modules]
    (m : ℕ) :
    Subsingleton
        (Ext.{u} (C := (Proj PS).Modules)
          (show (Proj PS).Modules from
            sectionRepresenter (Proj PS).ringCatSheaf (⊤ : Scheme.Opens (Proj PS)))
          (sheafOfModules PS m) 1) ∧
      Subsingleton
        (Ext.{u} (C := (Proj PS).Modules)
          (show (Proj PS).Modules from
            sectionRepresenter (Proj PS).ringCatSheaf (⊤ : Scheme.Opens (Proj PS)))
          (sheafOfModules PS m) 2) := by
  let U : ULift.{u} (Fin 4) → Scheme.Opens (Proj PS) :=
    fun i => p3StandardOpen (K := K) i.down
  have hU : (Opens.grothendieckTopology (Proj PS)).CoversTop U := by
    apply (Opens.coversTop_iff _ _).mpr
    apply TopologicalSpace.IsOpenCover.mk
    change (⨆ i : ULift.{u} (Fin 4), p3StandardOpen (K := K) i.down) = ⊤
    simpa [iSup_ulift] using p3StandardOpen_iSup K
  let hT : IsTerminal (⊤ : Scheme.Opens (Proj PS)) := isTerminalTop
  let S := sectionRepresenterCechAugmentationShortComplex
    (Proj PS).ringCatSheaf U (⊤ : Scheme.Opens (Proj PS)) hT
  let C₀ : (Proj PS).Modules := (sectionRepresenterCechChain (Proj PS).ringCatSheaf U).X 0
  let C₁ : (Proj PS).Modules := (sectionRepresenterCechChain (Proj PS).ringCatSheaf U).X 1
  let C₂ : (Proj PS).Modules := (sectionRepresenterCechChain (Proj PS).ringCatSheaf U).X 2
  let C₃ : (Proj PS).Modules := (sectionRepresenterCechChain (Proj PS).ringCatSheaf U).X 3
  let P : (Proj PS).Modules :=
    (sectionRepresenterCechAugmented (Proj PS).ringCatSheaf U
      (⊤ : Scheme.Opens (Proj PS)) hT).right
  let ε : C₀ ⟶ P := sectionRepresenterCechAugmentation
    (Proj PS).ringCatSheaf U (⊤ : Scheme.Opens (Proj PS)) hT
  let d₁ : C₁ ⟶ C₀ := (sectionRepresenterCechChain (Proj PS).ringCatSheaf U).d 1 0
  let d₂ : C₂ ⟶ C₁ := (sectionRepresenterCechChain (Proj PS).ringCatSheaf U).d 2 1
  let d₃ : C₃ ⟶ C₂ := (sectionRepresenterCechChain (Proj PS).ringCatSheaf U).d 3 2
  have haug := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    (Proj PS).ringCatSheaf U hU (⊤ : Scheme.Opens (Proj PS)) hT
  letI : Epi ε := by exact haug.2
  have hpos (n : ℕ) := sectionRepresenterCechChain_exactAt_succ_of_coversTop
    (Proj PS).ringCatSheaf U hU n
  have hexact₀ : (ShortComplex.mk d₁ ε S.zero).Exact := by
    exact haug.1
  have hexact₁ : (ShortComplex.mk d₂ d₁
      ((sectionRepresenterCechChain (Proj PS).ringCatSheaf U).d_comp_d 2 1 0)).Exact := by
    have hh := hpos 0
    rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)] at hh
    exact hh
  have hC₀₁ : Subsingleton (Ext.{u} (C := (Proj PS).Modules) C₀ (sheafOfModules PS m) 1) := by
    let V : ULift.{u} (Fin 4) → Scheme.Opens (Proj PS) :=
      fun i => p3StandardOpen (K := K) i.down
    letI h₁ : ∀ f : Fin 1 → ULift.{u} (Fin 4),
        Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sectionRepresenter (Proj PS).ringCatSheaf
          (∏ᶜ fun i => V (f i))) (sheafOfModules PS m) 1) := fun f => by
      let g : Fin 1 → Fin 4 := fun i => (f i).down
      let W : Scheme.Opens (Proj PS) := ⨅ i : Fin 1,
        p3StandardOpen (K := K) (g i)
      let hW := p3NegativeTwistCechInter_sectionRepresenter_ext_one_and_two_subsingleton
        K m 0 g
      letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sectionRepresenter (Proj PS).ringCatSheaf W)
          (sheafOfModules PS m) 1) := hW.1
      let e : W = ∏ᶜ fun i => V (f i) :=
        (p3CechProduct_eq_inf K 0 g).symm
      rw [← e]
      infer_instance
    dsimp [C₀, U]
    rw [sectionRepresenterCechChain_obj]
    exact ext_finite_coproduct_subsingleton (A := (Proj PS).Modules)
      (fun f : Fin 1 → ULift.{u} (Fin 4) =>
        sectionRepresenter (Proj PS).ringCatSheaf (∏ᶜ fun i => V (f i)))
      (sheafOfModules PS m) 1
  have hC₀₂ : Subsingleton (Ext.{u} (C := (Proj PS).Modules) C₀ (sheafOfModules PS m) 2) := by
    let V : ULift.{u} (Fin 4) → Scheme.Opens (Proj PS) :=
      fun i => p3StandardOpen (K := K) i.down
    letI h₂ : ∀ f : Fin 1 → ULift.{u} (Fin 4),
        Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sectionRepresenter (Proj PS).ringCatSheaf
          (∏ᶜ fun i => V (f i))) (sheafOfModules PS m) 2) := fun f => by
      let g : Fin 1 → Fin 4 := fun i => (f i).down
      let W : Scheme.Opens (Proj PS) := ⨅ i : Fin 1,
        p3StandardOpen (K := K) (g i)
      let hW := p3NegativeTwistCechInter_sectionRepresenter_ext_one_and_two_subsingleton
        K m 0 g
      letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sectionRepresenter (Proj PS).ringCatSheaf W)
          (sheafOfModules PS m) 2) := hW.2
      let e : W = ∏ᶜ fun i => V (f i) :=
        (p3CechProduct_eq_inf K 0 g).symm
      rw [← e]
      infer_instance
    dsimp [C₀, U]
    rw [sectionRepresenterCechChain_obj]
    exact ext_finite_coproduct_subsingleton (A := (Proj PS).Modules)
      (fun f : Fin 1 → ULift.{u} (Fin 4) =>
        sectionRepresenter (Proj PS).ringCatSheaf (∏ᶜ fun i => V (f i)))
      (sheafOfModules PS m) 2
  have hC₁₁ : Subsingleton (Ext.{u} (C := (Proj PS).Modules) C₁ (sheafOfModules PS m) 1) := by
    let V : ULift.{u} (Fin 4) → Scheme.Opens (Proj PS) :=
      fun i => p3StandardOpen (K := K) i.down
    letI h₁ : ∀ f : Fin 2 → ULift.{u} (Fin 4),
        Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sectionRepresenter (Proj PS).ringCatSheaf
          (∏ᶜ fun i => V (f i))) (sheafOfModules PS m) 1) := fun f => by
      let g : Fin 2 → Fin 4 := fun i => (f i).down
      let W : Scheme.Opens (Proj PS) := ⨅ i : Fin 2,
        p3StandardOpen (K := K) (g i)
      let hW := p3NegativeTwistCechInter_sectionRepresenter_ext_one_and_two_subsingleton
        K m 1 g
      letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules) (sectionRepresenter (Proj PS).ringCatSheaf W)
          (sheafOfModules PS m) 1) := hW.1
      let e : W = ∏ᶜ fun i => V (f i) :=
        (p3CechProduct_eq_inf K 1 g).symm
      rw [← e]
      infer_instance
    dsimp [C₁, U]
    rw [sectionRepresenterCechChain_obj]
    exact ext_finite_coproduct_subsingleton (A := (Proj PS).Modules)
      (fun f : Fin 2 → ULift.{u} (Fin 4) =>
        sectionRepresenter (Proj PS).ringCatSheaf (∏ᶜ fun i => V (f i)))
      (sheafOfModules PS m) 1
  have hHom₁ : Function.Exact
      (fun f : C₀ ⟶ sheafOfModules PS m => d₁ ≫ f)
      (fun f : C₁ ⟶ sheafOfModules PS m => d₂ ≫ f) := by
    exact p3SectionRepresenterCechHom_exact_one K m
  have hHom₂ : Function.Exact
      (fun f : C₁ ⟶ sheafOfModules PS m => d₂ ≫ f)
      (fun f : C₂ ⟶ sheafOfModules PS m => d₃ ≫ f) := by
    exact p3SectionRepresenterCechHom_exact_two K m
  letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules) C₀ (sheafOfModules PS m) 1) := hC₀₁
  letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules) C₀ (sheafOfModules PS m) 2) := hC₀₂
  letI : Subsingleton (Ext.{u} (C := (Proj PS).Modules) C₁ (sheafOfModules PS m) 1) := hC₁₁
  have h := ext_one_and_two_subsingleton_of_augmented_acyclic_chain
    (A := (Proj PS).Modules)
    (sheafOfModules PS m) P C₀ C₁ C₂ C₃ ε d₁ d₂ d₃
    S.zero
    ((sectionRepresenterCechChain (Proj PS).ringCatSheaf U).d_comp_d 2 1 0)
    ((sectionRepresenterCechChain (Proj PS).ringCatSheaf U).d_comp_d 3 2 1)
    hexact₀ hexact₁ hHom₁ hHom₂
  let eP : P ≅ (show (Proj PS).Modules from
      sectionRepresenter (Proj PS).ringCatSheaf (⊤ : Scheme.Opens (Proj PS))) :=
    ((FormalCoproduct.evalCompInclIsoId _ _).app
      (sectionRepresenterFunctor (Proj PS).ringCatSheaf)).app ⊤
  letI := h.1
  letI := h.2
  exact ⟨ext_subsingleton_of_iso_left (C := (Proj PS).Modules) eP 1,
    ext_subsingleton_of_iso_left (C := (Proj PS).Modules) eP 2⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every concrete negative twist on projective three-space has zero first
and second scheme-module cohomology. -/
theorem p3_negativeTwist_cohomology_one_and_two_subsingleton
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    Subsingleton (schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 1) ∧
      Subsingleton (schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 2) := by
  have h := p3_sectionRepresenter_ext_one_and_two_subsingleton K m
  letI := h.1
  letI := h.2
  exact ⟨ext_subsingleton_of_iso_left (C := (Proj PS).Modules) (Y := sheafOfModules PS m)
      (sectionRepresenterTopIsoUnit (Proj PS)) 1,
    ext_subsingleton_of_iso_left (C := (Proj PS).Modules) (Y := sheafOfModules PS m)
      (sectionRepresenterTopIsoUnit (Proj PS)) 2⟩

end PfaffianDescent.ProjectiveNegativeTwist
