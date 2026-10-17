import PfaffianDescent.ProjectiveChartGlobalUniversalFamilyPullback
import PfaffianDescent.ProjectiveChartGluedClassifierCoherence
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty

/-! Arbitrary-test injection of the literal original197 universal-family
pullback. Local chart factorizations are CONSTRUCTED by two nested native
cover pullbacks. Whole-family coherence and actual cover extensionality
then derive equality of the original maps. No local factor, cover,
matching or injectivity outcome is supplied as a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option autoImplicit false
variable {J : Type u} {X B : Scheme.{u}} (F : X ⟶ B) (U : J → X.Opens) (n : ℕ)
variable [IsSeparated F] (H : J → Over B)
variable (eta : ∀ i, relativeFiniteFlatHilbertFunctor197 ((U i).ι ≫ F) n ≅ yoneda.obj (H i))

/-- Actual chart of the pulled-back parameter cover, over the ORIGINAL B. -/
private def globalUniversalPullbackCoverTest001
    (T : Over B) (g : T ⟶ relativeOpenChartParameterGluedObject001 F U n H eta) (i : J) : Over B :=
  Over.mk (((relativeOpenChartParameterSchemeGlueData001 F U n H eta).openCover.pullback₁ g.left).f i ≫
    T.hom)

/-- Its actual inclusion over B, with the original base triangle literal. -/
private def globalUniversalPullbackCoverInclusion001
    (T : Over B) (g : T ⟶ relativeOpenChartParameterGluedObject001 F U n H eta) (i : J) :
    globalUniversalPullbackCoverTest001 F U n H eta T g i ⟶ T :=
  Over.homMk (((relativeOpenChartParameterSchemeGlueData001 F U n H eta).openCover.pullback₁ g.left).f i) rfl

/-- Native pullbackHom and the constructed chart/base square CONSTRUCT
its original classifier-chart factor in the slice, without a landing premise. -/
private def globalUniversalPullbackCoverChartFactor001
    (T : Over B) (g : T ⟶ relativeOpenChartParameterGluedObject001 F U n H eta) (i : J) :
    globalUniversalPullbackCoverTest001 F U n H eta T g i ⟶ H i := by
  let C : (relativeOpenChartParameterGluedObject001 F U n H eta).left.OpenCover :=
    (relativeOpenChartParameterSchemeGlueData001 F U n H eta).openCover
  let Cg : T.left.OpenCover := C.pullback₁ g.left
  let b : Cg.X i ⟶ (H i).left := C.pullbackHom g.left i
  have hBase : C.f i ≫ (relativeOpenChartParameterGluedObject001 F U n H eta).hom = (H i).hom :=
    relativeOpenChartParameterGluedToBase_chart001 F U n H eta i
  refine Over.homMk b ?_
  change b ≫ (H i).hom = (C.pullback₁ g.left).f i ≫ T.hom
  have h01 : b ≫ (H i).hom = (b ≫ C.f i) ≫
      (relativeOpenChartParameterGluedObject001 F U n H eta).hom :=
    (congrArg (fun q => b ≫ q) hBase).symm.trans
      (Category.assoc b (C.f i) (relativeOpenChartParameterGluedObject001 F U n H eta).hom).symm
  have h12 : (b ≫ C.f i) ≫ (relativeOpenChartParameterGluedObject001 F U n H eta).hom =
      (Cg.f i ≫ g.left) ≫ (relativeOpenChartParameterGluedObject001 F U n H eta).hom :=
    congrArg (fun q => q ≫ (relativeOpenChartParameterGluedObject001 F U n H eta).hom)
      (C.pullbackHom_map g.left i)
  have h23 : (Cg.f i ≫ g.left) ≫ (relativeOpenChartParameterGluedObject001 F U n H eta).hom =
      Cg.f i ≫ T.hom :=
    (Category.assoc (Cg.f i) g.left
      (relativeOpenChartParameterGluedObject001 F U n H eta).hom).trans
        (congrArg (fun q => Cg.f i ≫ q) (Over.w g))
  exact h01.trans (h12.trans h23)

/-- The constructed chart factor has the EXACT original restriction map
into the same glued parameter object. -/
private theorem globalUniversalPullbackCoverChartFactor_triangle001
    (T : Over B) (g : T ⟶ relativeOpenChartParameterGluedObject001 F U n H eta) (i : J) :
    globalUniversalPullbackCoverChartFactor001 F U n H eta T g i ≫
      relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i =
    globalUniversalPullbackCoverInclusion001 F U n H eta T g i ≫ g := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left]
  change (relativeOpenChartParameterSchemeGlueData001 F U n H eta).openCover.pullbackHom g.left i ≫
      (relativeOpenChartParameterSchemeGlueData001 F U n H eta).openCover.f i =
    ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).openCover.pullback₁ g.left).f i ≫ g.left
  exact (relativeOpenChartParameterSchemeGlueData001 F U n H eta).openCover.pullbackHom_map g.left i

/-- A bounded same-family cut on an actual local test. Every factor and
triangle in the public caller is constructed by the native covers above. -/
private theorem globalUniversalPullback_localClassified_eq001
    (T : Over B) (g h : T ⟶ relativeOpenChartParameterGluedObject001 F U n H eta)
    (heq : relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T g =
      relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T h)
    (S : Over B) (a : S ⟶ T) (i j : J) (gi : S ⟶ H i) (hj : S ⟶ H j)
    (hgi : gi ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i = a ≫ g)
    (hhj : hj ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j = a ≫ h) :
    relativeOpenChartClassifiedAmbientPoint001 F (U i) n (H i) (eta i) S gi =
      relativeOpenChartClassifiedAmbientPoint001 F (U j) n (H j) (eta j) S hj := by
  have hRestricted :
      relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta S (a ≫ g) =
      relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta S (a ≫ h) :=
    (relativeOpenChartParameterGlobalUniversalFamilyPullback_natural001 F U n H eta a g).trans
      ((congrArg (fun P => (relativeFiniteFlatHilbertFunctor197 F n).map a.op P) heq).trans
        (relativeOpenChartParameterGlobalUniversalFamilyPullback_natural001 F U n H eta a h).symm)
  calc
    _ = relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta S
        (gi ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i) :=
      (relativeOpenChartParameterGlobalUniversalFamilyPullback_chartRecovery001 F U n H eta i S gi).symm
    _ = relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta S (a ≫ g) :=
      congrArg (fun q => relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta S q) hgi
    _ = relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta S (a ≫ h) := hRestricted
    _ = relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta S
        (hj ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j) :=
      congrArg (fun q => relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta S q) hhj.symm
    _ = relativeOpenChartClassifiedAmbientPoint001 F (U j) n (H j) (eta j) S hj :=
      relativeOpenChartParameterGlobalUniversalFamilyPullback_chartRecovery001 F U n H eta j S hj

/-- On EVERY original scheme test, equality of the entire universal
pullback family determines the original global map. Native cover pullbacks
construct both local chart factors; no factorization/injection conclusion,
quasicompactness or reducedness certificate is a premise. -/
theorem relativeOpenChartParameterGlobalUniversalFamilyPullback_injective001 (T : Over B) :
    Function.Injective (relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U n H eta T) := by
  intro g h heq
  let C : (relativeOpenChartParameterGluedObject001 F U n H eta).left.OpenCover :=
    (relativeOpenChartParameterSchemeGlueData001 F U n H eta).openCover
  let Cg : T.left.OpenCover := C.pullback₁ g.left
  apply Over.OverMorphism.ext
  apply Scheme.Cover.hom_ext Cg g.left h.left
  intro i
  change J at i
  let Ti := globalUniversalPullbackCoverTest001 F U n H eta T g i
  let ai : Ti ⟶ T := globalUniversalPullbackCoverInclusion001 F U n H eta T g i
  let gi : Ti ⟶ H i := globalUniversalPullbackCoverChartFactor001 F U n H eta T g i
  let hi : Ti ⟶ relativeOpenChartParameterGluedObject001 F U n H eta := ai ≫ h
  let Ch : Ti.left.OpenCover := C.pullback₁ hi.left
  apply Scheme.Cover.hom_ext Ch (Cg.f i ≫ g.left) (Cg.f i ≫ h.left)
  intro j
  change J at j
  let S := globalUniversalPullbackCoverTest001 F U n H eta Ti hi j
  let bj : S ⟶ Ti := globalUniversalPullbackCoverInclusion001 F U n H eta Ti hi j
  let hj : S ⟶ H j := globalUniversalPullbackCoverChartFactor001 F U n H eta Ti hi j
  let a : S ⟶ T := bj ≫ ai
  have hTriangle : gi ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i = ai ≫ g :=
    globalUniversalPullbackCoverChartFactor_triangle001 F U n H eta T g i
  have hgi : (bj ≫ gi) ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i = a ≫ g := by
    calc
      _ = bj ≫ (gi ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i) :=
        Category.assoc _ _ _
      _ = bj ≫ (ai ≫ g) := congrArg (fun q => bj ≫ q) hTriangle
      _ = (bj ≫ ai) ≫ g := (Category.assoc bj ai g).symm
  have hhj : hj ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j = a ≫ h :=
    (globalUniversalPullbackCoverChartFactor_triangle001 F U n H eta Ti hi j).trans
      (Category.assoc bj ai h).symm
  have hFamily := globalUniversalPullback_localClassified_eq001 F U n H eta
    T g h heq S a i j (bj ≫ gi) hj hgi hhj
  have hSame := relativeOpenChartParameterGluedClassifier_eq_of_sameWholeFamily001 F U n H eta
    i j S (bj ≫ gi) hj hFamily
  have hRestriction : a ≫ g = a ≫ h := hgi.symm.trans (hSame.trans hhj)
  have hLeft := congrArg (fun f => f.left) hRestriction
  change (Ch.f j ≫ Cg.f i) ≫ g.left = (Ch.f j ≫ Cg.f i) ≫ h.left at hLeft
  exact (Category.assoc (Ch.f j) (Cg.f i) g.left).symm.trans
    (hLeft.trans (Category.assoc (Ch.f j) (Cg.f i) h.left))

end PfaffianDescent
end
