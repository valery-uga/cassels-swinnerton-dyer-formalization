import PfaffianDescent.PlanePositiveSectionRepresenterCechHomComparison
import PfaffianDescent.PlaneNegativeSectionRepresenterCechHomComparison
import PfaffianDescent.SectionRepresenterCechAugmentationExact
import PfaffianDescent.SectionRepresenterCechLocalExact
import PfaffianDescent.CechExtVanishingLowDegree
/-! SOURCE ONLY / UNCHECKED. Native P2 intrinsic low-degree cohomology,
derived from the SAME actual coordinate-cover augmentation, actual local
unit-frame acyclicity and actual native differential comparison. The two
public twist endpoints have no comparison/vanishing certificate premise. -/
noncomputable section
namespace PfaffianDescent.ProjectivePlaneNative
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry MvPolynomial Opposite TopologicalSpace
open ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 3) K
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native three-coordinate opens cover the actual native plane. -/
theorem p2StandardOpenLifted_coversTop :
    (Opens.grothendieckTopology (Proj PS)).CoversTop (p2StandardOpenLifted K) := by
  apply (Opens.coversTop_iff _ _).mpr
  apply TopologicalSpace.IsOpenCover.mk
  exact p2StandardOpenLifted_iSup K

/-- A bounded finite-coproduct cut for the SAME actual section-representer
chain. The local inputs concern its actual coordinate intersections. -/
theorem p2SectionRepresenterChain_ext_one_and_two_of_local
    [hExt : HasExt.{u} (Proj PS).Modules] (M : (Proj PS).Modules)
    (hlocal : ∀ (n : ℕ) (f : Fin (n + 1) → Fin 3),
      Subsingleton (Ext.{u} (C := (Proj PS).Modules)
        (show (Proj PS).Modules from sectionRepresenter (Proj PS).ringCatSheaf
          (⨅ i, p2StandardOpen (K := K) (f i))) M 1) ∧
      Subsingleton (Ext.{u} (C := (Proj PS).Modules)
        (show (Proj PS).Modules from sectionRepresenter (Proj PS).ringCatSheaf
          (⨅ i, p2StandardOpen (K := K) (f i))) M 2)) (n : ℕ) :
    Subsingleton (Ext.{u} (C := (Proj PS).Modules)
      ((p2SectionRepresenterCechChain K).X n) M 1) ∧
    Subsingleton (Ext.{u} (C := (Proj PS).Modules)
      ((p2SectionRepresenterCechChain K).X n) M 2) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  let V := p2StandardOpenLifted K
  let X : (Fin (n + 1) → P2CoordinateIndex.{u}) → (Proj PS).Modules :=
    fun f => sectionRepresenter (Proj PS).ringCatSheaf (∏ᶜ fun i => V (f i))
  have hterm (f : Fin (n + 1) → P2CoordinateIndex.{u}) :
      Subsingleton (Ext.{u} (C := (Proj PS).Modules) (X f) M 1) ∧
      Subsingleton (Ext.{u} (C := (Proj PS).Modules) (X f) M 2) := by
    let g : Fin (n + 1) → Fin 3 := fun i => (f i).down
    have h := hlocal n g
    have e : (⨅ i, p2StandardOpen (K := K) (g i)) = ∏ᶜ fun i => V (f i) :=
      (p2CechProduct_eq_inf K n g).symm
    simpa only [X, ← e] using h
  letI h₁ : ∀ f, Subsingleton (Ext.{u} (C := (Proj PS).Modules) (X f) M 1) :=
    fun f => (hterm f).1
  letI h₂ : ∀ f, Subsingleton (Ext.{u} (C := (Proj PS).Modules) (X f) M 2) :=
    fun f => (hterm f).2
  dsimp only [p2SectionRepresenterCechChain]
  rw [sectionRepresenterCechChain_obj]
  change Subsingleton (Ext.{u} (C := (Proj PS).Modules) (∐ X) M 1) ∧
    Subsingleton (Ext.{u} (C := (Proj PS).Modules) (∐ X) M 2)
  exact ⟨ext_finite_coproduct_subsingleton X M 1,
    ext_finite_coproduct_subsingleton X M 2⟩

/-- Generic bounded native resolution cut, used below with internally
proved local frames and internally proved native Hom exactness. -/
theorem p2_intrinsic_cohomology_one_and_two_of_actual_resolution
    [hExt : HasExt.{u} (Proj PS).Modules] (M : (Proj PS).Modules)
    (hlocal : ∀ (n : ℕ) (f : Fin (n + 1) → Fin 3),
      Subsingleton (Ext.{u} (C := (Proj PS).Modules)
        (show (Proj PS).Modules from sectionRepresenter (Proj PS).ringCatSheaf
          (⨅ i, p2StandardOpen (K := K) (f i))) M 1) ∧
      Subsingleton (Ext.{u} (C := (Proj PS).Modules)
        (show (Proj PS).Modules from sectionRepresenter (Proj PS).ringCatSheaf
          (⨅ i, p2StandardOpen (K := K) (f i))) M 2))
    (hHom₁ : Function.Exact
      (fun h : (p2SectionRepresenterCechChain K).X 0 ⟶ M =>
        (p2SectionRepresenterCechChain K).d 1 0 ≫ h)
      (fun h : (p2SectionRepresenterCechChain K).X 1 ⟶ M =>
        (p2SectionRepresenterCechChain K).d 2 1 ≫ h))
    (hHom₂ : Function.Exact
      (fun h : (p2SectionRepresenterCechChain K).X 1 ⟶ M =>
        (p2SectionRepresenterCechChain K).d 2 1 ≫ h)
      (fun h : (p2SectionRepresenterCechChain K).X 2 ⟶ M =>
        (p2SectionRepresenterCechChain K).d 3 2 ≫ h)) :
    Subsingleton (schemeModuleCohomology (Proj PS) M 1) ∧
    Subsingleton (schemeModuleCohomology (Proj PS) M 2) := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj PS).ringCatSheaf) := hExt
  let U := p2StandardOpenLifted K
  let C := p2SectionRepresenterCechChain K
  let P : (Proj PS).Modules :=
    (sectionRepresenterCechAugmented (Proj PS).ringCatSheaf U ⊤ isTerminalTop).right
  let ε : C.X 0 ⟶ P :=
    sectionRepresenterCechAugmentation (Proj PS).ringCatSheaf U ⊤ isTerminalTop
  have haug := sectionRepresenterCech_augmentation_exact_and_epi_of_coversTop
    (Proj PS).ringCatSheaf U (p2StandardOpenLifted_coversTop K) ⊤ isTerminalTop
  letI : Epi ε := haug.2
  have hpos := sectionRepresenterCechChain_exactAt_succ_of_coversTop
    (Proj PS).ringCatSheaf U (p2StandardOpenLifted_coversTop K) 0
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)] at hpos
  have h₀ := p2SectionRepresenterChain_ext_one_and_two_of_local K M hlocal 0
  have h₁ := p2SectionRepresenterChain_ext_one_and_two_of_local K M hlocal 1
  letI : Subsingleton (Ext.{u} (C.X 0) M 1) := h₀.1
  letI : Subsingleton (Ext.{u} (C.X 0) M 2) := h₀.2
  letI : Subsingleton (Ext.{u} (C.X 1) M 1) := h₁.1
  have h := ext_one_and_two_subsingleton_of_augmented_acyclic_chain
    (A := (Proj PS).Modules) M P (C.X 0) (C.X 1) (C.X 2) (C.X 3)
    ε (C.d 1 0) (C.d 2 1) (C.d 3 2)
    (sectionRepresenterCech_d_one_zero_comp_augmentation
      (Proj PS).ringCatSheaf U (⊤ : Scheme.Opens (Proj PS)) isTerminalTop)
    (C.d_comp_d 2 1 0) (C.d_comp_d 3 2 1) haug.1 hpos hHom₁ hHom₂
  letI : Subsingleton (Ext.{u} P M 1) := h.1
  letI : Subsingleton (Ext.{u} P M 2) := h.2
  exact ⟨ext_subsingleton_of_iso_left (C := (Proj PS).Modules)
      (Y := M) (schemeCoverCechTargetIsoUnit U) 1,
    ext_subsingleton_of_iso_left (C := (Proj PS).Modules)
      (Y := M) (schemeCoverCechTargetIsoUnit U) 2⟩

/-- ACTUAL native P2 positive-twist intrinsic H1/H2 vanish, without any
comparison, graded-piece or cohomology outcome as an input. -/
theorem p2_positiveTwist_cohomology_one_and_two_subsingleton
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) :
    Subsingleton (schemeModuleCohomology (Proj PS) (positiveSheafOfModules PS m) 1) ∧
    Subsingleton (schemeModuleCohomology (Proj PS) (positiveSheafOfModules PS m) 2) := by
  exact p2_intrinsic_cohomology_one_and_two_of_actual_resolution K
    (positiveSheafOfModules PS m)
    (fun n f => p2PositiveCechInter_sectionRepresenter_ext_one_and_two_subsingleton K m n f)
    (p2PositiveSectionRepresenterCechHom_exact_one K m)
    (p2PositiveSectionRepresenterCechHom_exact_two K m)

/-- The ACTUAL negative P2 twists needed for positive cubic restriction
have vanishing intrinsic H1/H2. Degree3 is deliberately excluded. -/
theorem p2_negativeTwist_cohomology_one_and_two_subsingleton_of_le_two
    [HasExt.{u} (Proj PS).Modules] (m : ℕ) (hm : m ≤ 2) :
    Subsingleton (schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 1) ∧
    Subsingleton (schemeModuleCohomology (Proj PS) (sheafOfModules PS m) 2) := by
  exact p2_intrinsic_cohomology_one_and_two_of_actual_resolution K
    (sheafOfModules PS m)
    (fun n f => p2NegativeCechInter_sectionRepresenter_ext_one_and_two_subsingleton K m n f)
    (p2NegativeSectionRepresenterCechHom_exact_one K m)
    (p2NegativeSectionRepresenterCechHom_exact_two K m hm)

end PfaffianDescent.ProjectivePlaneNative
