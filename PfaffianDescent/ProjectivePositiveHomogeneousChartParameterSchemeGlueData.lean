import PfaffianDescent.ProjectivePositiveHomogeneousChartNativeTripleCyclicIdentity
import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterSelfOverlap
import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterSelfReciprocalIdentity
import PfaffianDescent.NativeSchemeGlueDataDescent300
import PfaffianDescent.ProjectiveFiniteFamilyHomogeneousWholeOpenCover
import PfaffianDescent.ProjectivePositiveHomogeneousChartAllTestClassifier

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
variable {J : Type u} {X B : Scheme.{u}} (F : X ⟶ B) (U : J → X.Opens) (n : ℕ) [IsSeparated F]
variable (H : J → Over B)
variable (eta : ∀ i, relativeFiniteFlatHilbertFunctor197 ((U i).ι ≫ F) n ≅ yoneda.obj (H i))

/-- Explicit scheme morphism on the actual overlap schemes. The source
and target are fixed before this map is used in a dependent constructor. -/
private def actualChartOverlapSchemeTransition001 (i j : J) :
    (relativeOpenChartParameterOverlap001 F (U i) (U j) n (H i) (eta i)).toScheme ⟶
      (relativeOpenChartParameterOverlap001 F (U j) (U i) n (H j) (eta j)).toScheme :=
  (relativeOpenChartParameterOverlapReciprocalMap001 F (U i) (U j) n
    (H i) (H j) (eta i) (eta j)).left

/-- Typed scheme-level self identity, extracted before constructing the
native gluing datum so its dependent t-id field uses a bounded equality. -/
private theorem actualChartSelfReciprocalSchemeIdentity001 (i : J) :
    actualChartOverlapSchemeTransition001 F U n H eta i i =
        𝟙 (relativeOpenChartParameterOverlap001 F (U i) (U i) n (H i) (eta i)).toScheme := by
  exact congrArg
    (fun f : relativeOpenChartParameterOverlapTest001 F (U i) (U i) n (H i) (eta i) ⟶
        relativeOpenChartParameterOverlapTest001 F (U i) (U i) n (H i) (eta i) => f.left)
    (relativeOpenChartParameterSelfReciprocalMap_eq_id001 F (U i) n (H i) (eta i))

/-- Explicit native triple scheme map on the literal pullbacks of the
original open inclusions, constructed by the accepted Cartesian intake. -/
private def actualChartTripleSchemeMap001 (i j k : J) :
    pullback
      (relativeOpenChartParameterOverlap001 F (U i) (U j) n (H i) (eta i)).ι
      (relativeOpenChartParameterOverlap001 F (U i) (U k) n (H i) (eta i)).ι ⟶
    pullback
      (relativeOpenChartParameterOverlap001 F (U j) (U k) n (H j) (eta j)).ι
      (relativeOpenChartParameterOverlap001 F (U j) (U i) n (H j) (eta j)).ι :=
  relativeOpenChartParameterNativeTripleMap001 F (U i) (U j) (U k) n
    (H i) (H j) (eta i) (eta j)

/-- Typed factor equality for the actual triple map and scheme transition,
proved before either is inserted into the native gluing constructor. -/
private theorem actualChartTripleSchemeMapFactor001 (i j k : J) :
    actualChartTripleSchemeMap001 F U n H eta i j k ≫
      pullback.snd
        (relativeOpenChartParameterOverlap001 F (U j) (U k) n (H j) (eta j)).ι
        (relativeOpenChartParameterOverlap001 F (U j) (U i) n (H j) (eta j)).ι =
    pullback.fst
      (relativeOpenChartParameterOverlap001 F (U i) (U j) n (H i) (eta i)).ι
      (relativeOpenChartParameterOverlap001 F (U i) (U k) n (H i) (eta i)).ι ≫
        actualChartOverlapSchemeTransition001 F U n H eta i j :=
  relativeOpenChartParameterNativeTripleMap_snd001 F (U i) (U j) (U k) n
    (H i) (H j) (eta i) (eta j)

/-- Typed cyclic equality for the same explicitly constructed scheme maps.
No identity or cocycle premise is introduced by the constructor cut. -/
private theorem actualChartTripleSchemeMapCyclic001 (i j k : J) :
    actualChartTripleSchemeMap001 F U n H eta i j k ≫
      actualChartTripleSchemeMap001 F U n H eta j k i ≫
        actualChartTripleSchemeMap001 F U n H eta k i j =
    𝟙 (pullback
      (relativeOpenChartParameterOverlap001 F (U i) (U j) n (H i) (eta i)).ι
      (relativeOpenChartParameterOverlap001 F (U i) (U k) n (H i) (eta i)).ι) :=
  relativeOpenChartParameterNativeTripleMap_cyclic001 F (U i) (U j) (U k) n
    (H i) (H j) (H k) (eta i) (eta j) (eta k)

/-- CONSTRUCTED native Scheme gluing data of the SAME actual indexed chart
models. Every overlap, transition, self identity, triple map and cyclic
identity is derived internally. No gluing or matching outcome is supplied. -/
def relativeOpenChartParameterSchemeGlueData001 : Scheme.GlueData.{u} where
  J := J
  U i := (H i).left
  V ij := (relativeOpenChartParameterOverlap001 F (U ij.1) (U ij.2) n (H ij.1) (eta ij.1)).toScheme
  f i j := (relativeOpenChartParameterOverlap001 F (U i) (U j) n (H i) (eta i)).ι
  f_mono i j := by
    let W := relativeOpenChartParameterOverlap001 F (U i) (U j) n (H i) (eta i)
    letI : IsOpenImmersion W.ι :=
      inferInstanceAs (IsOpenImmersion ((H i).left.ofRestrict W.isOpenEmbedding))
    infer_instance
  f_hasPullback i j k := by infer_instance
  f_id i := (relativeOpenChartParameterSelfOverlap_eq_top001 F (U i) n (H i) (eta i)) ▸
    (Scheme.topIso (H i).left).isIso_hom
  t i j := actualChartOverlapSchemeTransition001 F U n H eta i j
  t_id i := actualChartSelfReciprocalSchemeIdentity001 F U n H eta i
  t' i j k := actualChartTripleSchemeMap001 F U n H eta i j k
  t_fac i j k := actualChartTripleSchemeMapFactor001 F U n H eta i j k
  cocycle i j k := actualChartTripleSchemeMapCyclic001 F U n H eta i j k
  f_open i j := by
    let W := relativeOpenChartParameterOverlap001 F (U i) (U j) n (H i) (eta i)
    exact inferInstanceAs (IsOpenImmersion ((H i).left.ofRestrict W.isOpenEmbedding))

/-- The actual glued Scheme, with its full native scheme structure. -/
def relativeOpenChartParameterGluedScheme001 : Scheme.{u} :=
  (relativeOpenChartParameterSchemeGlueData001 F U n H eta).glued

/-- Compatibility of the ORIGINAL base maps follows from the actual
reciprocal slice factor; no compatible-map or scalar-action premise is used. -/
theorem relativeOpenChartParameterSchemeGlueData_overBase001 (i j : J) :
    (relativeOpenChartParameterSchemeGlueData001 F U n H eta).t i j ≫
      (relativeOpenChartParameterSchemeGlueData001 F U n H eta).f j i ≫ (H j).hom =
    (relativeOpenChartParameterSchemeGlueData001 F U n H eta).f i j ≫ (H i).hom := by
  have h := congrArg (fun f => f.left)
    (relativeOpenChartParameterOverlapReciprocalMap_comp001 F (U i) (U j) n (H i) (H j) (eta i) (eta j))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ (H j).hom) h).trans
      (Over.w (relativeOpenChartParameterOverlapTransition001 F (U i) (U j) n (H i) (H j) (eta i) (eta j))))

/-- Native Scheme gluing descends the SAME original structure maps to B. -/
def relativeOpenChartParameterGluedToBase001 :
    relativeOpenChartParameterGluedScheme001 F U n H eta ⟶ B :=
  nativeSchemeGlueDataDesc300 (relativeOpenChartParameterSchemeGlueData001 F U n H eta) B
    (fun i => (H i).hom) (relativeOpenChartParameterSchemeGlueData_overBase001 F U n H eta)

/-- EXACT original-base chart equality for the constructed global Scheme. -/
theorem relativeOpenChartParameterGluedToBase_chart001 (i : J) :
    (relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι i ≫
      relativeOpenChartParameterGluedToBase001 F U n H eta = (H i).hom :=
  nativeSchemeGlueDataDesc_chart300 (relativeOpenChartParameterSchemeGlueData001 F U n H eta) B
    (fun i => (H i).hom) (relativeOpenChartParameterSchemeGlueData_overBase001 F U n H eta) i

/-- The actual parameter Scheme in the ORIGINAL slice category. -/
def relativeOpenChartParameterGluedObject001 : Over B :=
  Over.mk (relativeOpenChartParameterGluedToBase001 F U n H eta)

/-- Actual original-model chart inclusion OVER B; its left map is
DEFINITIONALLY the native gluing inclusion, with no model reselection. -/
def relativeOpenChartParameterGluedChartInclusionOver001 (i : J) :
    H i ⟶ relativeOpenChartParameterGluedObject001 F U n H eta :=
  Over.homMk ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι i)
    (relativeOpenChartParameterGluedToBase_chart001 F U n H eta i)

/-- Explicit exact left-map API for the actual chart inclusion. -/
theorem relativeOpenChartParameterGluedChartInclusionOver_left001 (i : J) :
    (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i).left =
      (relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι i := rfl

/-- The ACTUAL native pair overlap is Cartesian in the constructed Scheme;
this follows from native gluing's proved limit, not a comparison premise. -/
theorem relativeOpenChartParameterGlued_pairCartesian001 (i j : J) :
    IsPullback ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).f i j)
      ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).t i j ≫
        (relativeOpenChartParameterSchemeGlueData001 F U n H eta).f j i)
      ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι i)
      ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι j) :=
  IsPullback.of_isLimit ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).vPullbackConeIsLimit i j)

/-- Cartesian pair square uses EXACTLY the original overlap slice inclusion
and original classifier transition expected by the whole-family dictionary. -/
theorem relativeOpenChartParameterGlued_pairSliceCartesian001 (i j : J) :
    IsPullback (relativeOpenChartParameterOverlapInclusion001 F (U i) (U j) n (H i) (eta i)).left
      (relativeOpenChartParameterOverlapTransition001 F (U i) (U j) n (H i) (H j) (eta i) (eta j)).left
      (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i).left
      (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j).left := by
  have h := relativeOpenChartParameterGlued_pairCartesian001 F U n H eta i j
  change IsPullback
    (relativeOpenChartParameterOverlapInclusion001 F (U i) (U j) n (H i) (eta i)).left
    ((relativeOpenChartParameterOverlapReciprocalMap001 F (U i) (U j) n (H i) (H j) (eta i) (eta j)).left ≫
      (relativeOpenChartParameterOverlapInclusion001 F (U j) (U i) n (H j) (eta j)).left)
    (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i).left
    (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j).left at h
  have hPair := congrArg (fun f => f.left)
    (relativeOpenChartParameterOverlapReciprocalMap_comp001 F (U i) (U j) n (H i) (H j) (eta i) (eta j))
  simp only [Over.comp_left] at hPair
  rw [hPair] at h
  exact h

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {σ : Type} [Finite σ]
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))

/-- Actual representing object for each ORIGINAL positive homogeneous
chart is CHOSEN INTERNALLY from its already proved construction, once per index. -/
def originalPositiveHomogeneousChartIndexRepresentingObject001 (n : ℕ) (hn : 0 < n)
    (a : projectivePositiveHomogeneousChartIndex001 (grading I)) : Over (Spec (.of R)) :=
  Classical.choose (originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I a.val
    (Classical.choose a.property) (Classical.choose_spec a.property).1 (Classical.choose_spec a.property).2 n hn)

/-- Its internally constructed classifier, retaining exactly that SAME
chosen object for every pair and triple transition. -/
def originalPositiveHomogeneousChartIndexRepresentingIso001 (n : ℕ) (hn : 0 < n)
    (a : projectivePositiveHomogeneousChartIndex001 (grading I)) :
    relativeFiniteFlatHilbertFunctor197 ((Proj.basicOpen (grading I) a.val).ι ≫ toBase I) n ≅
      yoneda.obj (originalPositiveHomogeneousChartIndexRepresentingObject001 I n hn a) :=
  Classical.choice (Classical.choose_spec
    (originalPositiveHomogeneousChart_exists_allTestHilbertRepresentingIso001 I a.val
      (Classical.choose a.property) (Classical.choose_spec a.property).1 (Classical.choose_spec a.property).2 n hn))

/-- Genuine gluing datum of ALL original positive homogeneous chart models;
no models, classifiers, cover, gluing or matching outcome is a premise. -/
def originalPositiveHomogeneousParameterSchemeGlueData001 (n : ℕ) (hn : 0 < n) : Scheme.GlueData.{u} :=
  relativeOpenChartParameterSchemeGlueData001 (toBase I)
    (fun a : projectivePositiveHomogeneousChartIndex001 (grading I) => Proj.basicOpen (grading I) a.val)
    n (originalPositiveHomogeneousChartIndexRepresentingObject001 I n hn)
    (originalPositiveHomogeneousChartIndexRepresentingIso001 I n hn)

/-- The CONSTRUCTED all-positive-chart parameter Scheme over ORIGINAL R.
Global whole universal family/NatIso/LFP are separate derived next steps. -/
def originalPositiveHomogeneousParameterGluedToBase001 (n : ℕ) (hn : 0 < n) :
    (originalPositiveHomogeneousParameterSchemeGlueData001 I n hn).glued ⟶ Spec (.of R) :=
  relativeOpenChartParameterGluedToBase001 (toBase I)
    (fun a : projectivePositiveHomogeneousChartIndex001 (grading I) => Proj.basicOpen (grading I) a.val)
    n (originalPositiveHomogeneousChartIndexRepresentingObject001 I n hn)
    (originalPositiveHomogeneousChartIndexRepresentingIso001 I n hn)

end PfaffianDescent
end
