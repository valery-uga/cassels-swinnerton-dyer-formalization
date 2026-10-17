import PfaffianDescent.CorayActualPositiveNativeChartZeroDetection
import PfaffianDescent.CorayActualPositiveNativeIdealGeneratorFactor
import PfaffianDescent.CorayActualAmbientIdealPositiveInclusionMono
import PfaffianDescent.CorayActualPositiveGlobalPresentationExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! The original positive generator genuinely presents the OWN ideal twist.
Native chart factors derive the global image and epimorphism. No image,
section-surjectivity or Serre-vanishing certificate is assumed.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
open BundleSectionZeroLocus IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PolyA" => MvPolynomial (Fin 4) K
local notation "PS" => homogeneousSubmodule (Fin 4) K

private lemma mappedComposite_zero_of_factor
    {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {M J O Z : C} (g : M ⟶ O) (v : J ⟶ O)
    (b : F.obj M ⟶ F.obj J) (z : O ⟶ Z)
    (hb : b ≫ F.map v = F.map g) (hz : v ≫ z = 0) :
    F.map (g ≫ z) = 0 := by
  have h₁ : F.map (g ≫ z) = (b ≫ F.map v) ≫ F.map z :=
    (F.map_comp g z).trans (congrArg (fun w => w ≫ F.map z) hb.symm)
  have h₂ : (b ≫ F.map v) ≫ F.map z = b ≫ F.map (v ≫ z) :=
    (Category.assoc b (F.map v) (F.map z)).trans
      (congrArg (fun w => b ≫ w) (F.map_comp v z).symm)
  have h₃ : b ≫ F.map (v ≫ z) = 0 := by
    rw [hz, F.map_zero J Z, comp_zero]
  exact h₁.trans (h₂.trans h₃)

private theorem exists_epiFactor_of_jointZero
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} {D : ι → Type*} [∀ i, Category (D i)] [∀ i, HasZeroMorphisms (D i)]
    (F : ∀ i, C ⥤ D i) [∀ i, (F i).PreservesZeroMorphisms]
    (detect : ∀ {M N : C} (f : M ⟶ N), (∀ i, (F i).map f = 0) → f = 0)
    {M J O : C} (v : J ⟶ O) [Mono v] (g : M ⟶ O)
    (b : ∀ i, (F i).obj M ⟶ (F i).obj J)
    (hb : ∀ i, b i ≫ (F i).map v = (F i).map g)
    (hmono : ∀ i, Mono ((F i).map v)) (hepi : ∀ i, Epi (b i)) :
    ∃ a : M ⟶ J, a ≫ v = g ∧ Epi a := by
  have hg : g ≫ cokernel.π v = 0 := detect _ (fun i =>
    mappedComposite_zero_of_factor (F i) g v (b i) (cokernel.π v)
      (hb i) (cokernel.condition v))
  let a := Abelian.monoLift v g hg
  have ha : a ≫ v = g := Abelian.monoLift_comp v g hg
  have halocal : ∀ i, (F i).map a = b i := by
    intro i
    letI : Mono ((F i).map v) := hmono i
    apply (cancel_mono ((F i).map v)).mp
    exact ((F i).map_comp a v).symm.trans
      ((congrArg (F i).map ha).trans (hb i).symm)
  have hEpi : Epi a := NormalMonoCategory.epi_of_zero_cancel a (fun Z k hak => by
    apply detect k
    intro i
    letI : Epi (b i) := hepi i
    apply (cancel_epi (b i)).mp
    have hlocal : b i ≫ (F i).map k = 0 :=
      (congrArg (fun w => w ≫ (F i).map k) (halocal i).symm).trans
        (((F i).map_comp a k).symm.trans
          ((congrArg (F i).map hak).trans ((F i).map_zero M Z)))
    exact hlocal.trans comp_zero.symm)
  exact ⟨a, ha, hEpi⟩

private theorem exactIdealFactor_of_exactIntoAmbient
    {C : Type*} [Category C] [Abelian C]
    {L M J O : C} (r : L ⟶ M) (g : M ⟶ O)
    (v : J ⟶ O) [Mono v] (a : M ⟶ J) (ha : a ≫ v = g)
    (hz : r ≫ g = 0) (h : (ShortComplex.mk r g hz).Exact) :
    ∃ hz' : r ≫ a = 0, (ShortComplex.mk r a hz').Exact := by
  have hz' : r ≫ a = 0 := by
    apply (cancel_mono v).mp
    exact (Category.assoc r a v).trans
      ((congrArg (fun w => r ≫ w) ha).trans (hz.trans zero_comp.symm))
  let S := ShortComplex.mk r a hz'
  let T := ShortComplex.mk r g hz
  let φ : S ⟶ T :=
    { τ₁ := 𝟙 L
      τ₂ := 𝟙 M
      τ₃ := v
      comm₁₂ := by
        change (𝟙 L) ≫ r = r ≫ (𝟙 M)
        simp only [Category.id_comp, Category.comp_id]
      comm₂₃ := by
        change (𝟙 M) ≫ g = a ≫ v
        simpa only [Category.id_comp] using ha.symm }
  have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr h
  exact ⟨hz', hS⟩

/-- The SAME positive generator factors epimorphically through the ACTUAL
whole ideal tensor O(m). Native normalized generator surjectivity, chart
inclusion compatibility, and zero detection construct the factor internally.
The constructed witness is the canonical Abelian.monoLift, not a supplied
map or image-identification certificate. -/
theorem actualPositiveFiniteGeneratorMap_exists_epiIdealFactor
    (I : HomogeneousIdeal PS) {ι : Type u} [Fintype ι]
    (g : ι → PolyA) (d : ι → ℕ) (hhom : ∀ i, (g i).IsHomogeneous (d i))
    (hg : Ideal.span (Set.range g) = I.toIdeal)
    (m : ℕ) (hm : ∀ i, d i ≤ m) :
    ∃ a : (∐ fun i => positiveSheafOfModules PS (m - d i)) ⟶
      schemeModuleTensor (closedImmersionModule (quotientProjMap I))
        (positiveSheafOfModules PS m),
      a ≫ actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m) =
        actualPositiveFiniteGeneratorMap g d hhom m hm ∧ Epi a := by
  let D (j : Fin 4) :=
    (Spec (CommRingCat.of (HomogeneousLocalization.Away PS (X j)))).Modules
  let F (j : Fin 4) : (Proj PS).Modules ⥤ D j := Scheme.Modules.pullback
    (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))
  let v := actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m)
  let G := actualPositiveFiniteGeneratorMap g d hhom m hm
  let b (j : Fin 4) := actualPositiveNativeIdealGeneratorFactor I g d hhom hg m hm j
  letI : ∀ j, (F j).IsLeftAdjoint := fun j =>
    (Scheme.Modules.pullbackPushforwardAdjunction
      (Proj.awayι PS (X j) (isHomogeneous_X K j) (by decide : 0 < 1))).isLeftAdjoint
  letI : ∀ j, (F j).PreservesZeroMorphisms := fun j =>
    Functor.preservesZeroMorphisms_of_isLeftAdjoint (F j)
  letI : Mono v := actualAmbientIdealPositiveInclusion_mono I m
  exact exists_epiFactor_of_jointZero F
    (fun {_ _} f h => actualPositiveNativeCharts_jointlyDetectZero f h) v G b
    (fun j => actualPositiveNativeIdealGeneratorFactor_inclusion I g d hhom hg m hm j)
    (fun j => actualAmbientIdealPositiveInclusion_nativeChart_mono I j m)
    (fun j => actualPositiveNativeIdealGeneratorFactor_epi I g d hhom hg m hm j)

/-- The SAME whole ideal twist is genuinely finitely presented by the
original weighted generator and relation maps. Exactness and the final epi
are derived, with no desired Serre/global-section-surjectivity premise. -/
theorem actualPositiveFinitePresentation_exists_exact_epiIdealFactor
    (I : HomogeneousIdeal PS) {ι κ : Type u} [Fintype ι] [Fintype κ]
    (g : ι → PolyA) (d : ι → ℕ) (hg : ∀ i, (g i).IsHomogeneous (d i))
    (r : κ → ι → PolyA) (e : κ → ℕ)
    (hr : ∀ a, ActualWeightedPolynomialHomogeneous d (e a) (r a))
    (hspanG : Ideal.span (Set.range g) = I.toIdeal)
    (hspanR : Submodule.span PolyA (Set.range r) = (actualPolynomialGeneratorMap g).ker)
    (m : ℕ) (hd : ∀ i, d i ≤ m) (he : ∀ a, e a ≤ m) :
    ∃ a : (∐ fun i => positiveSheafOfModules PS (m - d i)) ⟶
      schemeModuleTensor (closedImmersionModule (quotientProjMap I))
        (positiveSheafOfModules PS m),
      Epi a ∧
      a ≫ actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m) =
        actualPositiveFiniteGeneratorMap g d hg m hd ∧
      ∃ hz : actualPositiveFiniteRelationMap d r e hr m he ≫ a = 0,
        (ShortComplex.mk (actualPositiveFiniteRelationMap d r e hr m he) a hz).Exact := by
  obtain ⟨a, ha, hepi⟩ :=
    actualPositiveFiniteGeneratorMap_exists_epiIdealFactor I g d hg hspanG m hd
  let v := actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m)
  letI : Mono v := actualAmbientIdealPositiveInclusion_mono I m
  let S := actualPositiveFinitePresentationComplex g d hg r e hr
    (actualPresentationRelation_mem_kernel g r hspanR) m hd he
  have hS : S.Exact := actualPositiveFinitePresentationComplex_exact
    I g d hg r e hr hspanG hspanR m hd he
  have hfactor := @exactIdealFactor_of_exactIntoAmbient (Proj PS).Modules _ _
    S.X₁ S.X₂ _ _ S.f S.g v (actualAmbientIdealPositiveInclusion_mono I m)
    a ha S.zero hS
  exact ⟨a, hepi, ha, hfactor⟩

/-- Every whole homogeneous ideal internally supplies this genuine ideal
presentation in all degrees above its finite weights. No polynomial
presentation, ideal-image equality or vanishing conclusion is an input. -/
theorem homogeneousIdeal_exists_actualPositiveExactEpiIdealPresentation
    (I : HomogeneousIdeal PS) :
    ∃ (T : Finset PolyA) (d : T → ℕ) (R : Finset (T → PolyA)) (e : R → ℕ) (B : ℕ)
      (hg : ∀ i : T, (i : PolyA).IsHomogeneous (d i))
      (hr : ∀ a : R, ActualWeightedPolynomialHomogeneous d (e a) a.val),
      Ideal.span (T : Set PolyA) = I.toIdeal ∧
      Submodule.span PolyA (R : Set (T → PolyA)) =
        (actualPolynomialGeneratorMap (fun i : T => i.val)).ker ∧
      (∀ i : T, d i ≤ B) ∧ (∀ a : R, e a ≤ B) ∧
      ∀ (m : ℕ) (hd : ∀ i : T, d i ≤ m) (he : ∀ a : R, e a ≤ m),
        ∃ a : (∐ fun i : T => positiveSheafOfModules PS (m - d i)) ⟶
          schemeModuleTensor (closedImmersionModule (quotientProjMap I))
            (positiveSheafOfModules PS m),
          Epi a ∧
          a ≫ actualIdealTwistInclusion (quotientProjMap I) (positiveSheafOfModules PS m) =
            actualPositiveFiniteGeneratorMap (fun i : T => i.val) d hg m hd ∧
          ∃ hz : actualPositiveFiniteRelationMap d (fun a : R => a.val) e hr m he ≫ a = 0,
            (ShortComplex.mk (actualPositiveFiniteRelationMap d (fun a : R => a.val)
              e hr m he) a hz).Exact := by
  classical
  obtain ⟨T, d, R, e, B, hT, hd, hR, he, hker, hchart⟩ :=
    homogeneousIdeal_exists_actualPositiveFiniteCoproductPresentationData I
  have hTset : Set.range (fun i : T => i.val) = (T : Set PolyA) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩; exact i.property
    · intro ha; exact ⟨⟨a, ha⟩, rfl⟩
  have hRset : Set.range (fun a : R => a.val) = (R : Set (T → PolyA)) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩; exact i.property
    · intro ha; exact ⟨⟨a, ha⟩, rfl⟩
  have hspanG : Ideal.span (Set.range (fun i : T => i.val)) = I.toIdeal := by
    rw [hTset]; exact hT
  have hspanR : Submodule.span PolyA (Set.range (fun a : R => a.val)) =
      (actualPolynomialGeneratorMap (fun i : T => i.val)).ker := by
    rw [hRset]; exact hR
  refine ⟨T, d, R, e, B, fun i => (hd i).2, fun a => (he a).2,
    hT, hR, fun i => (hd i).1, fun a => (he a).1, ?_⟩
  intro m hdm hem
  exact actualPositiveFinitePresentation_exists_exact_epiIdealFactor
    I (fun i : T => i.val) d (fun i => (hd i).2)
    (fun a : R => a.val) e (fun a => (he a).2) hspanG hspanR m hdm hem

end PfaffianDescent.Coray
