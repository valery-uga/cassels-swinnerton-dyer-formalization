import PfaffianDescent.ProjectiveFiniteFamilyAllTestLocalChartDictionary
import PfaffianDescent.ProjectiveChartGluedClassifierCoherence
import PfaffianDescent.ProjectiveChartGlobalUniversalFamilyPullback
import PfaffianDescent.RelativeHilbertTestCoverUniqueness309
import AllCharacteristics.HomogeneousConfigurationQuotient

/-! Construct the actual global classifying map on EVERY original test.
The original family constructs the6305 cover and literal local chart points;
same197 restrictions derive classifier compatibility, and native scheme
Hom gluing constructs the original-base map. Its entire family is recovered
as the literal global universal pullback. No lift/cover/matching is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u v w
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Abstract composition application is isolated before any concrete
geometric functor or constructed original point is substituted. -/
private theorem actualForwardFunctor_comp_apply001
    {C : Type v} [Category.{w} C] (A : Cᵒᵖ ⥤ Type u)
    {T W V : C} (g : T ⟶ W) (t : W ⟶ V) (P : A.obj (.op V)) :
    A.map (g ≫ t).op P = A.map g.op (A.map t.op P) := by
  simpa only [op_comp, types_comp_apply] using ConcreteCategory.congr_hom (A.map_comp t.op g.op) P

/-- Abstract inverse classifier law, before the concrete local point. -/
private theorem actualForwardTypeNatIso_hom_inv_apply001
    {C : Type v} [Category.{w} C] {A D : C ⥤ Type u}
    (e : A ≅ D) (T : C) (P : A.obj T) : e.inv.app T (e.hom.app T P) = P := by
  simpa only [types_comp_apply, types_id_apply] using
    ConcreteCategory.congr_hom (e.hom_inv_id_app T) P

/-- The literal intersection of two actual test-cover members, over the
SAME original base. No affine or quasi-compact test premise is used. -/
private def actualForwardCoverPairTest001 {B : Scheme.{u}}
    (T : Over B) (C : T.left.OpenCover.{u}) (i j : C.I₀) : Over B :=
  Over.mk (pullback.fst (C.f i) (C.f j) ≫ (C.f i ≫ T.hom))

private def actualForwardCoverPairFstOver001 {B : Scheme.{u}}
    (T : Over B) (C : T.left.OpenCover.{u}) (i j : C.I₀) :
    actualForwardCoverPairTest001 T C i j ⟶ relativeHilbertTestCoverObject309 T C i :=
  Over.homMk (pullback.fst (C.f i) (C.f j)) rfl

private def actualForwardCoverPairSndOver001 {B : Scheme.{u}}
    (T : Over B) (C : T.left.OpenCover.{u}) (i j : C.I₀) :
    actualForwardCoverPairTest001 T C i j ⟶ relativeHilbertTestCoverObject309 T C j := by
  refine Over.homMk (pullback.snd (C.f i) (C.f j)) ?_
  change pullback.snd (C.f i) (C.f j) ≫ (C.f j ≫ T.hom) =
    pullback.fst (C.f i) (C.f j) ≫ (C.f i ≫ T.hom)
  rw [← Category.assoc, ← Category.assoc, pullback.condition]

private theorem actualForwardCoverPair_comp_inclusions001 {B : Scheme.{u}}
    (T : Over B) (C : T.left.OpenCover.{u}) (i j : C.I₀) :
    actualForwardCoverPairFstOver001 T C i j ≫ relativeHilbertTestCoverMap309 T C i =
      actualForwardCoverPairSndOver001 T C i j ≫ relativeHilbertTestCoverMap309 T C j := by
  apply Over.OverMorphism.ext
  exact pullback.condition

variable {A : Type u} [CommRing A]
variable {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {B : Scheme.{u}} (F : Proj 𝒜 ⟶ B) (n : ℕ) [IsSeparated F]
variable (H : projectivePositiveHomogeneousChartIndex001 𝒜 → Over B)
variable (eta : ∀ a : projectivePositiveHomogeneousChartIndex001 𝒜,
  relativeFiniteFlatHilbertFunctor197 ((Proj.basicOpen 𝒜 a.val).ι ≫ F) n ≅ yoneda.obj (H a))
local notation "U𝒜" => (fun a : projectivePositiveHomogeneousChartIndex001 𝒜 => Proj.basicOpen 𝒜 (Subtype.val a))
variable (T : Over B) (P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F T) n)

/-- The SAME chosen local classifier of the chart point constructed by
the original whole-family dictionary on its actual cover member. -/
def relativePositiveHomogeneousLocalClassifyingMap001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a ⟶ H a :=
  (eta a).hom.app (.op (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a))
    (projectiveFiniteFamilyAllTestLocalChartPoint001 𝒜 F n T P a)

/-- Inverse classification recovers EXACTLY the literal original197
restriction, from the dictionary's full-point push identity. -/
theorem relativePositiveHomogeneousLocalClassifyingMap_wholeFamily001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    relativeOpenChartClassifiedAmbientPoint001 F (Proj.basicOpen 𝒜 a.val) n (H a) (eta a)
      (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)
      (relativePositiveHomogeneousLocalClassifyingMap001 𝒜 F n H eta T P a) =
        projectiveFiniteFamilyAllTestLocalRestriction001 𝒜 F n T P a := by
  have hInv := actualForwardTypeNatIso_hom_inv_apply001 (eta a)
    (.op (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a))
    (projectiveFiniteFamilyAllTestLocalChartPoint001 𝒜 F n T P a)
  change relativeOpenFiniteFlatPointPush315 (Proj.basicOpen 𝒜 a.val) F n
      (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a)
      ((eta a).inv.app (.op (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a))
        ((eta a).hom.app (.op (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a))
          (projectiveFiniteFamilyAllTestLocalChartPoint001 𝒜 F n T P a))) = _
  rw [hInv]
  exact projectiveFiniteFamilyAllTestLocalChartPoint_push_eq_restriction001 𝒜 F n T P a

/-- Actual local map into the constructed SAME global parameter scheme. -/
def relativePositiveHomogeneousLocalClassifyingSchemeMap001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    (projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).X a ⟶
      relativeOpenChartParameterGluedScheme001 F U𝒜 n H eta :=
  (relativePositiveHomogeneousLocalClassifyingMap001 𝒜 F n H eta T P a ≫
    relativeOpenChartParameterGluedChartInclusionOver001 F U𝒜 n H eta a).left

/-- Compatibility is DERIVED on the actual6305 cover intersections:
both whole families are the SAME literal197 restriction of P. -/
theorem relativePositiveHomogeneousLocalClassifyingSchemeMap_compatible001
    (i j : projectivePositiveHomogeneousChartIndex001 𝒜) :
    pullback.fst ((projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).f i)
        ((projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).f j) ≫
      relativePositiveHomogeneousLocalClassifyingSchemeMap001 𝒜 F n H eta T P i =
    pullback.snd ((projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).f i)
        ((projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).f j) ≫
      relativePositiveHomogeneousLocalClassifyingSchemeMap001 𝒜 F n H eta T P j := by
  let C := projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P
  let Tij := actualForwardCoverPairTest001 T C i j
  let ai := actualForwardCoverPairFstOver001 T C i j
  let aj := actualForwardCoverPairSndOver001 T C i j
  let gi := relativePositiveHomogeneousLocalClassifyingMap001 𝒜 F n H eta T P i
  let gj := relativePositiveHomogeneousLocalClassifyingMap001 𝒜 F n H eta T P j
  have hFamily : relativeOpenChartClassifiedAmbientPoint001 F (U𝒜 i) n (H i) (eta i) Tij (ai ≫ gi) =
      relativeOpenChartClassifiedAmbientPoint001 F (U𝒜 j) n (H j) (eta j) Tij (aj ≫ gj) := by
    let P0 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Tij) n :=
      relativeOpenChartClassifiedAmbientPoint001 F (U𝒜 i) n (H i) (eta i) Tij (ai ≫ gi)
    let P1 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Tij) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map ai.op
        (relativeOpenChartClassifiedAmbientPoint001 F (U𝒜 i) n (H i) (eta i)
          (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P i) gi)
    let P2 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Tij) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map ai.op
        (projectiveFiniteFamilyAllTestLocalRestriction001 𝒜 F n T P i)
    let P3 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Tij) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map
        (ai ≫ relativeHilbertTestCoverMap309 T C i).op P
    let P4 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Tij) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map
        (aj ≫ relativeHilbertTestCoverMap309 T C j).op P
    let P5 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Tij) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map aj.op
        (projectiveFiniteFamilyAllTestLocalRestriction001 𝒜 F n T P j)
    let P6 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Tij) n :=
      (relativeFiniteFlatHilbertFunctor197 F n).map aj.op
        (relativeOpenChartClassifiedAmbientPoint001 F (U𝒜 j) n (H j) (eta j)
          (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P j) gj)
    let P7 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Tij) n :=
      relativeOpenChartClassifiedAmbientPoint001 F (U𝒜 j) n (H j) (eta j) Tij (aj ≫ gj)
    have h01 : P0 = P1 := relativeOpenChartClassifiedAmbientPoint_natural001
      F (U𝒜 i) n (H i) (eta i) ai gi
    have h12 : P1 = P2 := congrArg
      (fun Q : FiniteFlatHilbertPoint195
          (relativeHilbertFamily197 F (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P i)) n =>
        (relativeFiniteFlatHilbertFunctor197 F n).map ai.op Q)
      (relativePositiveHomogeneousLocalClassifyingMap_wholeFamily001 𝒜 F n H eta T P i)
    have h23 : P2 = P3 := (actualForwardFunctor_comp_apply001
      (relativeFiniteFlatHilbertFunctor197 F n) ai (relativeHilbertTestCoverMap309 T C i) P).symm
    have h34 : P3 = P4 := congrArg
      (fun q : Tij ⟶ T => (relativeFiniteFlatHilbertFunctor197 F n).map q.op P)
      (actualForwardCoverPair_comp_inclusions001 T C i j)
    have h45 : P4 = P5 := actualForwardFunctor_comp_apply001
      (relativeFiniteFlatHilbertFunctor197 F n) aj (relativeHilbertTestCoverMap309 T C j) P
    have h56 : P5 = P6 := congrArg
      (fun Q : FiniteFlatHilbertPoint195
          (relativeHilbertFamily197 F (projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P j)) n =>
        (relativeFiniteFlatHilbertFunctor197 F n).map aj.op Q)
      (relativePositiveHomogeneousLocalClassifyingMap_wholeFamily001 𝒜 F n H eta T P j).symm
    have h67 : P6 = P7 := (relativeOpenChartClassifiedAmbientPoint_natural001
      F (U𝒜 j) n (H j) (eta j) aj gj).symm
    exact h01.trans (h12.trans (h23.trans (h34.trans (h45.trans (h56.trans h67)))))

  have hMaps := relativeOpenChartParameterGluedClassifier_eq_of_sameWholeFamily001
    F U𝒜 n H eta i j Tij (ai ≫ gi) (aj ≫ gj) hFamily
  change ai.left ≫ (gi ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U𝒜 n H eta i).left =
    aj.left ≫ (gj ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U𝒜 n H eta j).left
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f.left) hMaps).trans (Category.assoc _ _ _))

/-- Native scheme Hom gluing constructs the genuine global map from the
actual whole-family cover and the internally derived compatibility. -/
def relativePositiveHomogeneousGlobalClassifyingSchemeMap001 :
    T.left ⟶ relativeOpenChartParameterGluedScheme001 F U𝒜 n H eta :=
  (projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).glueMorphisms
    (relativePositiveHomogeneousLocalClassifyingSchemeMap001 𝒜 F n H eta T P)
    (relativePositiveHomogeneousLocalClassifyingSchemeMap_compatible001 𝒜 F n H eta T P)

theorem relativePositiveHomogeneousGlobalClassifyingSchemeMap_chart001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    (projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).f a ≫
      relativePositiveHomogeneousGlobalClassifyingSchemeMap001 𝒜 F n H eta T P =
        relativePositiveHomogeneousLocalClassifyingSchemeMap001 𝒜 F n H eta T P a :=
  (projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).ι_glueMorphisms _ _ a

/-- The global map preserves the SAME original base, tested on the
actual cover and derived from the local original slice maps. -/
theorem relativePositiveHomogeneousGlobalClassifyingSchemeMap_toBase001 :
    relativePositiveHomogeneousGlobalClassifyingSchemeMap001 𝒜 F n H eta T P ≫
      relativeOpenChartParameterGluedToBase001 F U𝒜 n H eta = T.hom := by
  apply (projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).hom_ext
  intro a
  change projectivePositiveHomogeneousChartIndex001 𝒜 at a
  have hChart := relativePositiveHomogeneousGlobalClassifyingSchemeMap_chart001 𝒜 F n H eta T P a
  have hBase : relativePositiveHomogeneousLocalClassifyingSchemeMap001 𝒜 F n H eta T P a ≫
      relativeOpenChartParameterGluedToBase001 F U𝒜 n H eta =
      (projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).f a ≫ T.hom :=
    Over.w (relativePositiveHomogeneousLocalClassifyingMap001 𝒜 F n H eta T P a ≫
      relativeOpenChartParameterGluedChartInclusionOver001 F U𝒜 n H eta a)
  exact (Category.assoc
    ((projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P).f a)
    (relativePositiveHomogeneousGlobalClassifyingSchemeMap001 𝒜 F n H eta T P)
    (relativeOpenChartParameterGluedToBase001 F U𝒜 n H eta)).symm.trans
      ((congrArg (fun q => q ≫ relativeOpenChartParameterGluedToBase001 F U𝒜 n H eta) hChart).trans hBase)

/-- The actual global classifier in the ORIGINAL slice, on ANY test. -/
def relativePositiveHomogeneousGlobalClassifyingMap001 :
    T ⟶ relativeOpenChartParameterGluedObject001 F U𝒜 n H eta :=
  Over.homMk (relativePositiveHomogeneousGlobalClassifyingSchemeMap001 𝒜 F n H eta T P)
    (relativePositiveHomogeneousGlobalClassifyingSchemeMap_toBase001 𝒜 F n H eta T P)

theorem relativePositiveHomogeneousGlobalClassifyingMap_chart001
    (a : projectivePositiveHomogeneousChartIndex001 𝒜) :
    projectiveFiniteFamilyAllTestLocalCoverInclusion001 𝒜 F n T P a ≫
      relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T P =
    relativePositiveHomogeneousLocalClassifyingMap001 𝒜 F n H eta T P a ≫
      relativeOpenChartParameterGluedChartInclusionOver001 F U𝒜 n H eta a := by
  apply Over.OverMorphism.ext
  exact relativePositiveHomogeneousGlobalClassifyingSchemeMap_chart001 𝒜 F n H eta T P a

/-- The WHOLE original family is recovered by literal global universal
pullback, using arbitrary-test cover uniqueness309. No recovery is assumed. -/
theorem relativePositiveHomogeneousGlobalClassifyingMap_pullback001 :
    relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U𝒜 n H eta T
      (relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T P) = P := by
  apply relativeHilbertPoint_eq_of_testCover309 F T
    (projectiveFiniteFamilyAllTestLocalCover001 𝒜 F n T P) n
  intro a
  change projectivePositiveHomogeneousChartIndex001 𝒜 at a
  let Ta := projectiveFiniteFamilyAllTestLocalCoverTest001 𝒜 F n T P a
  let inc := projectiveFiniteFamilyAllTestLocalCoverInclusion001 𝒜 F n T P a
  let g := relativePositiveHomogeneousGlobalClassifyingMap001 𝒜 F n H eta T P
  let ga := relativePositiveHomogeneousLocalClassifyingMap001 𝒜 F n H eta T P a
  let P0 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Ta) n :=
    (relativeFiniteFlatHilbertFunctor197 F n).map inc.op
      (relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U𝒜 n H eta T g)
  let P1 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Ta) n :=
    relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U𝒜 n H eta Ta (inc ≫ g)
  let P2 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Ta) n :=
    relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U𝒜 n H eta Ta
      (ga ≫ relativeOpenChartParameterGluedChartInclusionOver001 F U𝒜 n H eta a)
  let P3 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Ta) n :=
    relativeOpenChartClassifiedAmbientPoint001 F (U𝒜 a) n (H a) (eta a) Ta ga
  let P4 : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F Ta) n :=
    projectiveFiniteFamilyAllTestLocalRestriction001 𝒜 F n T P a
  have h01 : P0 = P1 :=
    (relativeOpenChartParameterGlobalUniversalFamilyPullback_natural001 F U𝒜 n H eta inc g).symm
  have h12 : P1 = P2 := congrArg
    (fun q : Ta ⟶ relativeOpenChartParameterGluedObject001 F U𝒜 n H eta =>
      relativeOpenChartParameterGlobalUniversalFamilyPullback001 F U𝒜 n H eta Ta q)
    (relativePositiveHomogeneousGlobalClassifyingMap_chart001 𝒜 F n H eta T P a)
  have h23 : P2 = P3 :=
    relativeOpenChartParameterGlobalUniversalFamilyPullback_chartRecovery001 F U𝒜 n H eta a Ta ga
  have h34 : P3 = P4 :=
    relativePositiveHomogeneousLocalClassifyingMap_wholeFamily001 𝒜 F n H eta T P a
  exact h01.trans (h12.trans (h23.trans h34))

/-- Actual original projective quotients construct the global classifying
map internally, with ALL-positive models chosen by actualD ONCE. -/
def originalPositiveHomogeneousGlobalClassifyingMap001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {τ : Type} [Finite τ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule τ R))
    (n : ℕ) (hn : 0 < n) (T : Over (Spec (.of R)))
    (P : FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (toBase I) T) n) :
    T ⟶ Over.mk (originalPositiveHomogeneousParameterGluedToBase001 I n hn) := by
  have hSeparated : IsSeparated
      (show Proj (grading I) ⟶ Spec (.of R) from toBase I) := isSeparated_homogeneousToBase I
  exact @relativePositiveHomogeneousGlobalClassifyingMap001
    (CoordinateRing I) inferInstance
    (Submodule R (CoordinateRing I)) inferInstance inferInstance
    (grading I) (AllCharacteristics.HomogeneousProjective.gradedRing I)
    (Spec (.of R)) (show Proj (grading I) ⟶ Spec (.of R) from toBase I) n hSeparated
    (originalPositiveHomogeneousChartIndexRepresentingObject001 I n hn)
    (originalPositiveHomogeneousChartIndexRepresentingIso001 I n hn) T P

end PfaffianDescent
end
