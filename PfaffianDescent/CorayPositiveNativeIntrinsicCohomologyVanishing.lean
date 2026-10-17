import PfaffianDescent.CorayPositiveNativeLocalExtVanishing
import PfaffianDescent.CorayPositiveNativeSectionRepresenterComparison
import PfaffianDescent.VoisinP3TopCechExtComparison

/-! Intrinsic cohomology vanishing for the OWN actual positive twists on
projective three-space, derived through the SAME native coordinate cover
and actual section-representer resolution. No cohomology vanishing or
comparison is a premise. SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry MvPolynomial Opposite
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Every term of the section-representer Cech chain is Ext-acyclic through
degree three against the SAME concrete positive twist. -/
theorem p3PositiveNativeSectionRepresenterChain_ext_one_two_three_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] (m n : ℕ) :
      Subsingleton
        (Ext.{u} (C := (Proj PS).Modules)
          ((p3SectionRepresenterCechChain K).X n)
          (positiveSheafOfModules PS m) 1) ∧
      Subsingleton
        (Ext.{u} (C := (Proj PS).Modules)
          ((p3SectionRepresenterCechChain K).X n)
          (positiveSheafOfModules PS m) 2) ∧
      Subsingleton
        (Ext.{u} (C := (Proj PS).Modules)
          ((p3SectionRepresenterCechChain K).X n)
          (positiveSheafOfModules PS m) 3) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  let V : ULift.{u} (Fin 4) → Scheme.Opens (Proj PS) :=
    fun i => p3StandardOpen (K := K) i.down
  let X : (Fin (n + 1) → ULift.{u} (Fin 4)) → (Proj PS).Modules :=
    fun f => sectionRepresenter (Proj PS).ringCatSheaf (∏ᶜ fun i => V (f i))
  have hlocal (f : Fin (n + 1) → ULift.{u} (Fin 4)) :
      Subsingleton (Ext.{u} (C := (Proj PS).Modules)
        (X f) (positiveSheafOfModules PS m) 1) ∧
      Subsingleton (Ext.{u} (C := (Proj PS).Modules)
        (X f) (positiveSheafOfModules PS m) 2) ∧
      Subsingleton (Ext.{u} (C := (Proj PS).Modules)
        (X f) (positiveSheafOfModules PS m) 3) := by
    let g : Fin (n + 1) → Fin 4 := fun i => (f i).down
    let W : Scheme.Opens (Proj PS) :=
      ⨅ i, p3StandardOpen (K := K) (g i)
    have hW :=
      p3PositiveNativeCechInter_sectionRepresenter_ext_one_two_three_subsingleton
        K m n g
    have e : W = ∏ᶜ fun i => V (f i) :=
      (p3CechProduct_eq_inf K n g).symm
    simpa only [X, ← e] using hW
  letI h₁ : ∀ f, Subsingleton
      (Ext.{u} (C := (Proj PS).Modules)
        (X f) (positiveSheafOfModules PS m) 1) :=
    fun f => (hlocal f).1
  letI h₂ : ∀ f, Subsingleton
      (Ext.{u} (C := (Proj PS).Modules)
        (X f) (positiveSheafOfModules PS m) 2) :=
    fun f => (hlocal f).2.1
  letI h₃ : ∀ f, Subsingleton
      (Ext.{u} (C := (Proj PS).Modules)
        (X f) (positiveSheafOfModules PS m) 3) :=
    fun f => (hlocal f).2.2
  dsimp only [p3SectionRepresenterCechChain]
  rw [sectionRepresenterCechChain_obj]
  change
    Subsingleton (Ext.{u} (C := (Proj PS).Modules)
      (∐ X) (positiveSheafOfModules PS m) 1) ∧
    Subsingleton (Ext.{u} (C := (Proj PS).Modules)
      (∐ X) (positiveSheafOfModules PS m) 2) ∧
    Subsingleton (Ext.{u} (C := (Proj PS).Modules)
      (∐ X) (positiveSheafOfModules PS m) 3)
  exact ⟨
    ext_finite_coproduct_subsingleton X (positiveSheafOfModules PS m) 1,
    ext_finite_coproduct_subsingleton X (positiveSheafOfModules PS m) 2,
    ext_finite_coproduct_subsingleton X (positiveSheafOfModules PS m) 3⟩

/-- The SAME actual standard-cover augmentation has vanishing Ext in
low degrees against every actual positive twist. -/
theorem p3PositiveNativeSectionRepresenterTarget_ext_one_two_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    Subsingleton (Ext.{u} (p3SectionRepresenterCechTarget K)
      (positiveSheafOfModules PS m) 1) ∧
    Subsingleton (Ext.{u} (p3SectionRepresenterCechTarget K)
      (positiveSheafOfModules PS m) 2) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  let C := p3SectionRepresenterCechChain K
  let P := p3SectionRepresenterCechTarget K
  let Y := positiveSheafOfModules PS m
  let ε := p3SectionRepresenterCechAugmentation K
  let U : ULift.{u} (Fin 4) → Scheme.Opens (Proj PS) :=
    fun i => p3StandardOpen (K := K) i.down
  have hlocal₀ :=
    p3PositiveNativeSectionRepresenterChain_ext_one_two_three_subsingleton K m 0
  have hlocal₁ :=
    p3PositiveNativeSectionRepresenterChain_ext_one_two_three_subsingleton K m 1
  letI : Subsingleton (Ext.{u} (C.X 0) Y 1) := hlocal₀.1
  letI : Subsingleton (Ext.{u} (C.X 0) Y 2) := hlocal₀.2.1
  letI : Subsingleton (Ext.{u} (C.X 1) Y 1) := hlocal₁.1
  letI : Epi ε := (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  exact ext_one_and_two_subsingleton_of_augmented_acyclic_chain
    (A := (Proj PS).Modules) Y P (C.X 0) (C.X 1) (C.X 2) (C.X 3)
    ε (C.d 1 0) (C.d 2 1) (C.d 3 2)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj PS).ringCatSheaf U (⊤ : Scheme.Opens (Proj PS)) isTerminalTop)
    (C.d_comp_d 2 1 0) (C.d_comp_d 3 2 1)
    (p3SectionRepresenterCech_augmentation_exact K)
    (p3SectionRepresenterCech_exact_one K)
    (p3PositiveSectionRepresenterCechHom_exact_one K m)
    (p3PositiveSectionRepresenterCechHom_exact_two K m)

/-- Every actual third Ext class of the SAME augmentation target is zero:
its actual Hom cocycle is an internally derived positive-twist boundary. -/
theorem p3PositiveNativeSectionRepresenterTarget_ext_three_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    Subsingleton (Ext.{u} (p3SectionRepresenterCechTarget K)
      (positiveSheafOfModules PS m) 3) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  let C := p3SectionRepresenterCechChain K
  let P := p3SectionRepresenterCechTarget K
  let Y := positiveSheafOfModules PS m
  let ε := p3SectionRepresenterCechAugmentation K
  let U : ULift.{u} (Fin 4) → Scheme.Opens (Proj PS) :=
    fun i => p3StandardOpen (K := K) i.down
  let h₁₀ : C.d 1 0 ≫ ε = 0 :=
    sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj PS).ringCatSheaf U (⊤ : Scheme.Opens (Proj PS)) isTerminalTop
  let h₂₁ := C.d_comp_d 2 1 0
  let h₃₂ := C.d_comp_d 3 2 1
  let h₄₃ := C.d_comp_d 4 3 2
  let h₀ : (ShortComplex.mk (C.d 1 0) ε h₁₀).Exact :=
    p3SectionRepresenterCech_augmentation_exact K
  let h₁ : (ShortComplex.mk (C.d 2 1) (C.d 1 0) h₂₁).Exact :=
    p3SectionRepresenterCech_exact_one K
  let h₂ : (ShortComplex.mk (C.d 3 2) (C.d 2 1) h₃₂).Exact :=
    p3SectionRepresenterCech_exact_two K
  let h₃ : (ShortComplex.mk (C.d 4 3) (C.d 3 2) h₄₃).Exact :=
    p3SectionRepresenterCech_exact_three K
  have hlocal₀ :=
    p3PositiveNativeSectionRepresenterChain_ext_one_two_three_subsingleton K m 0
  have hlocal₁ :=
    p3PositiveNativeSectionRepresenterChain_ext_one_two_three_subsingleton K m 1
  have hlocal₂ :=
    p3PositiveNativeSectionRepresenterChain_ext_one_two_three_subsingleton K m 2
  letI : Subsingleton (Ext.{u} (C.X 0) Y 2) := hlocal₀.2.1
  letI : Subsingleton (Ext.{u} (C.X 0) Y 3) := hlocal₀.2.2
  letI : Subsingleton (Ext.{u} (C.X 1) Y 1) := hlocal₁.1
  letI : Subsingleton (Ext.{u} (C.X 1) Y 2) := hlocal₁.2.1
  letI : Subsingleton (Ext.{u} (C.X 2) Y 1) := hlocal₂.1
  letI : Epi ε := (p3SectionRepresenterCech_augmentation_exact_and_epi K).2
  apply subsingleton_of_forall_eq 0
  intro z
  obtain ⟨f, hf⟩ := augmentedChainDegreeThreeToExt_surjective
    P (C.X 0) (C.X 1) (C.X 2) (C.X 3) (C.X 4) Y
    ε (C.d 1 0) (C.d 2 1) (C.d 3 2) (C.d 4 3)
    h₁₀ h₂₁ h₃₂ h₄₃ h₀ h₁ h₂ h₃ z
  have hboundary : ∃ q : C.X 2 ⟶ Y, C.d 3 2 ≫ q = f.1 :=
    (p3PositiveSectionRepresenterCechHom_exact_three K m f.1).mp f.2
  have hzero := (augmentedChainDegreeThreeToExt_eq_zero_iff
    P (C.X 0) (C.X 1) (C.X 2) (C.X 3) (C.X 4) Y
    ε (C.d 1 0) (C.d 2 1) (C.d 3 2) (C.d 4 3)
    h₁₀ h₂₁ h₃₂ h₄₃ h₀ h₁ h₂ h₃ f).mpr hboundary
  exact hf.symm.trans hzero

/-- Every OWN positive twist has zero intrinsic first, second and third
scheme-module cohomology over the original projective space. No scalar
action is changed: these are the actual native Ext carriers. -/
theorem p3_positiveTwist_cohomology_one_two_three_subsingleton
    [hExt : HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    Subsingleton (schemeModuleCohomology (Proj PS) (positiveSheafOfModules PS m) 1) ∧
    Subsingleton (schemeModuleCohomology (Proj PS) (positiveSheafOfModules PS m) 2) ∧
    Subsingleton (schemeModuleCohomology (Proj PS) (positiveSheafOfModules PS m) 3) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  have hlow := p3PositiveNativeSectionRepresenterTarget_ext_one_two_subsingleton K m
  letI : Subsingleton (Ext.{u} (p3SectionRepresenterCechTarget K)
      (positiveSheafOfModules PS m) 1) := hlow.1
  letI : Subsingleton (Ext.{u} (p3SectionRepresenterCechTarget K)
      (positiveSheafOfModules PS m) 2) := hlow.2
  letI : Subsingleton (Ext.{u} (p3SectionRepresenterCechTarget K)
      (positiveSheafOfModules PS m) 3) :=
    p3PositiveNativeSectionRepresenterTarget_ext_three_subsingleton K m
  exact ⟨
    ext_subsingleton_of_iso_left (C := (Proj PS).Modules)
      (Y := positiveSheafOfModules PS m) (p3SectionRepresenterCechTargetIsoUnit K) 1,
    ext_subsingleton_of_iso_left (C := (Proj PS).Modules)
      (Y := positiveSheafOfModules PS m) (p3SectionRepresenterCechTargetIsoUnit K) 2,
    ext_subsingleton_of_iso_left (C := (Proj PS).Modules)
      (Y := positiveSheafOfModules PS m) (p3SectionRepresenterCechTargetIsoUnit K) 3⟩

end PfaffianDescent.ProjectiveNegativeTwist
