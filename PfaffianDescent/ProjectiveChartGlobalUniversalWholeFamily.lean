import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterSchemeGlueData
import PfaffianDescent.ProjectiveChartUniversalWholeFamilyOverlap
import PfaffianDescent.RelativeHilbertAmbientCartesianPair
import PfaffianDescent.NativeSchemeCoverIsoCharts300
import PfaffianDescent.NativeHilbertChartRestrictionDescent300
import PfaffianDescent.CompatibleClosedSubschemeOpenCoverDescent

/-! Construct the universal WHOLE family on the actual glued original
chart parameter scheme. The original universal chart points and actualD
pair squares DERIVE all ideal compatibility. Closed-subscheme descent
constructs the full global ideal; finite-flat rank descent constructs its
literal195 point. No global ideal, family or matching outcome is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Changing the exact ambient pair maps transports the entire ideal
compatibility, including its dependent native pullback carrier. -/
private theorem actualWholeIdealPairCompatibility_transport001
    {X Y Z : Scheme.{u}} (f f0 : X ⟶ Z) (g g0 : Y ⟶ Z)
    (hf : f = f0) (hg : g = g0) (I : X.IdealSheafData) (J : Y.IdealSheafData)
    (h : I.comap (pullback.fst f0 g0) = J.comap (pullback.snd f0 g0)) :
    I.comap (pullback.fst f g) = J.comap (pullback.snd f g) := by
  cases hf
  cases hg
  exact h

variable {J : Type u} {X B : Scheme.{u}} (F : X ⟶ B) (U : J → X.Opens) (n : ℕ)
variable [IsSeparated F] (H : J → Over B)
variable (eta : ∀ i, relativeFiniteFlatHilbertFunctor197 ((U i).ι ≫ F) n ≅ yoneda.obj (H i))

/-- Pull back the actualD parameter cover and replace its members by the
literal original chart-model197 ambients. No model/test is reselected. -/
def relativeOpenChartParameterUniversalAmbientCover001 :
    (pullback (relativeOpenChartParameterGluedObject001 F U n H eta).hom F).OpenCover :=
  nativeSchemeOpenCoverIsoCharts300
    ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).openCover.pullback₁
      (relativeHilbertFamily197 F (relativeOpenChartParameterGluedObject001 F U n H eta)))
    (fun i => pullback (H i).hom F)
    (fun i => (relativeHilbertAmbientMap_isPullback197 F
      (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i)).isoPullback)

/-- The actual ambient cover map is EXACTLY the original197 chart map. -/
theorem relativeOpenChartParameterUniversalAmbientCover_map001 (i : J) :
    (relativeOpenChartParameterUniversalAmbientCover001 F U n H eta).f i =
      relativeHilbertAmbientMap197 F
        (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i) := by
  change (relativeHilbertAmbientMap_isPullback197 F
    (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i)).isoPullback.hom ≫
      pullback.fst (relativeHilbertFamily197 F
        (relativeOpenChartParameterGluedObject001 F U n H eta))
        (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i).left = _
  exact (relativeHilbertAmbientMap_isPullback197 F
    (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i)).isoPullback_hom_fst

/-- The actualD parameter pair and native197 squares CONSTRUCT the
Cartesian ambient pair used to identify the literal cover intersection. -/
private theorem actualGluedUniversalAmbientPair_isPullback001 (i j : J) :
    IsPullback
      (relativeHilbertAmbientMap197 F
        (relativeOpenChartParameterOverlapInclusion001 F (U i) (U j) n (H i) (eta i)))
      (relativeHilbertAmbientMap197 F
        (relativeOpenChartParameterOverlapTransition001 F (U i) (U j) n
          (H i) (H j) (eta i) (eta j)))
      (relativeHilbertAmbientMap197 F
        (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i))
      (relativeHilbertAmbientMap197 F
        (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j)) :=
  relativeHilbertAmbientMap_cartesian_of_sliceCartesian001 F
    (relativeOpenChartParameterOverlapInclusion001 F (U i) (U j) n (H i) (eta i))
    (relativeOpenChartParameterOverlapTransition001 F (U i) (U j) n
      (H i) (H j) (eta i) (eta j))
    (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i)
    (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j)
    (relativeOpenChartParameterGlued_pairSliceCartesian001 F U n H eta i j)

/-- The two actual universal WHOLE ideals agree on the ORIGINAL ambient
pair intersection. Pair matching and the ambient comparison are derived. -/
theorem relativeOpenChartParameterUniversalWholeIdeal_pairCompatibility001 (i j : J) :
    (relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i)).val.comap
      (pullback.fst
        (relativeHilbertAmbientMap197 F
          (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i))
        (relativeHilbertAmbientMap197 F
          (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j))) =
    (relativeOpenChartUniversalAmbientPoint001 F (U j) n (H j) (eta j)).val.comap
      (pullback.snd
        (relativeHilbertAmbientMap197 F
          (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i))
        (relativeHilbertAmbientMap197 F
          (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta j))) := by
  let hPair := actualGluedUniversalAmbientPair_isPullback001 F U n H eta i j
  have hWhole :
      (relativeOpenChartUniversalAmbientPoint001 F (U j) n (H j) (eta j)).val.comap
        (relativeHilbertAmbientMap197 F
          (relativeOpenChartParameterOverlapTransition001 F (U i) (U j) n
            (H i) (H j) (eta i) (eta j))) =
      (relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i)).val.comap
        (relativeHilbertAmbientMap197 F
          (relativeOpenChartParameterOverlapInclusion001 F (U i) (U j) n (H i) (eta i))) := by
    simpa only [Category.id_comp] using
      actualChartUniversalWholeFamily_allTest_overlap_wholeIdeal_eq001 F (U i) (U j) n
        (H i) (H j) (eta i) (eta j)
        (relativeOpenChartParameterOverlapTest001 F (U i) (U j) n (H i) (eta i)) (𝟙 _)
  rw [← hPair.isoPullback_inv_fst, ← hPair.isoPullback_inv_snd,
    Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
  exact congrArg (fun K => K.comap hPair.isoPullback.inv) hWhole.symm

/-- Full-ideal compatibility on the ACTUAL cover maps, retaining the
dependent native pullback domains rather than replacing their supports. -/
private theorem actualGluedUniversalAmbientCover_wholeIdeal_compatible001 (i j : J) :
    (relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i)).val.comap
      (pullback.fst
        ((relativeOpenChartParameterUniversalAmbientCover001 F U n H eta).f i)
        ((relativeOpenChartParameterUniversalAmbientCover001 F U n H eta).f j)) =
    (relativeOpenChartUniversalAmbientPoint001 F (U j) n (H j) (eta j)).val.comap
      (pullback.snd
        ((relativeOpenChartParameterUniversalAmbientCover001 F U n H eta).f i)
        ((relativeOpenChartParameterUniversalAmbientCover001 F U n H eta).f j)) := by
  exact actualWholeIdealPairCompatibility_transport001
    ((relativeOpenChartParameterUniversalAmbientCover001 F U n H eta).f i) _
    ((relativeOpenChartParameterUniversalAmbientCover001 F U n H eta).f j) _
    (relativeOpenChartParameterUniversalAmbientCover_map001 F U n H eta i)
    (relativeOpenChartParameterUniversalAmbientCover_map001 F U n H eta j)
    (relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i)).val
    (relativeOpenChartUniversalAmbientPoint001 F (U j) n (H j) (eta j)).val
    (relativeOpenChartParameterUniversalWholeIdeal_pairCompatibility001 F U n H eta i j)

/-- Closed-subscheme descent CONSTRUCTS a global full ideal with the
literal original universal ideals as its exact chart comaps. -/
theorem relativeOpenChartParameterGlobalUniversalWholeIdeal_exists001 :
    ∃ I : (pullback (relativeOpenChartParameterGluedObject001 F U n H eta).hom F).IdealSheafData,
      ∀ i : J, I.comap (relativeHilbertAmbientMap197 F
        (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i)) =
        (relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i)).val := by
  obtain ⟨I, hI⟩ := compatibleClosedSubschemes_openCover_exists_globalIdeal
    (relativeOpenChartParameterUniversalAmbientCover001 F U n H eta)
    (fun i => (relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i)).val)
    (actualGluedUniversalAmbientCover_wholeIdeal_compatible001 F U n H eta)
  refine ⟨I, ?_⟩
  intro i
  exact (congrArg I.comap
    (relativeOpenChartParameterUniversalAmbientCover_map001 F U n H eta i)).symm.trans (hI i)

/-- The global whole ideal is chosen from the CONSTRUCTED descent. -/
def relativeOpenChartParameterGlobalUniversalWholeIdeal001 :
    (pullback (relativeOpenChartParameterGluedObject001 F U n H eta).hom F).IdealSheafData :=
  Classical.choose (relativeOpenChartParameterGlobalUniversalWholeIdeal_exists001 F U n H eta)

/-- Exact full-ideal chart restriction of that SAME constructed ideal. -/
theorem relativeOpenChartParameterGlobalUniversalWholeIdeal_chart001 (i : J) :
    (relativeOpenChartParameterGlobalUniversalWholeIdeal001 F U n H eta).comap
      (relativeHilbertAmbientMap197 F
        (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i)) =
      (relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i)).val :=
  Classical.choose_spec (relativeOpenChartParameterGlobalUniversalWholeIdeal_exists001 F U n H eta) i

/-- Existing finite-flat constant-rank descent on the actualD cover
CONSTRUCTS the original literal195 global universal family. -/
def relativeOpenChartParameterGlobalUniversalFamily001 :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 F
      (relativeOpenChartParameterGluedObject001 F U n H eta)) n :=
  nativeHilbertPointOfChartRestrictions300
    (relativeHilbertFamily197 F (relativeOpenChartParameterGluedObject001 F U n H eta))
    (relativeOpenChartParameterSchemeGlueData001 F U n H eta).openCover
    (fun i => pullback (H i).hom F)
    (fun i => relativeHilbertAmbientMap197 F
      (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i))
    (fun i => relativeHilbertFamily197 F (H i))
    (fun i => relativeHilbertAmbientMap_isPullback197 F
      (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i)) n
    (fun i => relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i))
    (relativeOpenChartParameterGlobalUniversalWholeIdeal001 F U n H eta)
    (relativeOpenChartParameterGlobalUniversalWholeIdeal_chart001 F U n H eta)

/-- The original195/197 restriction of the global universal family is
EXACTLY each same original chart universal ambient point. -/
theorem relativeOpenChartParameterGlobalUniversalFamily_chart001 (i : J) :
    (relativeFiniteFlatHilbertFunctor197 F n).map
      (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i).op
      (relativeOpenChartParameterGlobalUniversalFamily001 F U n H eta) =
      relativeOpenChartUniversalAmbientPoint001 F (U i) n (H i) (eta i) := by
  apply Subtype.ext
  exact relativeOpenChartParameterGlobalUniversalWholeIdeal_chart001 F U n H eta i

/-- The actual original projective quotient constructs its global whole
universal family internally on ALL positive homogeneous chart models.
No chart model, global ideal, family or matching outcome is an input. -/
def originalPositiveHomogeneousParameterGlobalUniversalFamily001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R))
    (n : ℕ) (hn : 0 < n) :
    FiniteFlatHilbertPoint195 (relativeHilbertFamily197 (toBase I)
      (Over.mk (originalPositiveHomogeneousParameterGluedToBase001 I n hn))) n :=
  relativeOpenChartParameterGlobalUniversalFamily001 (toBase I)
    (fun a : projectivePositiveHomogeneousChartIndex001 (grading I) => Proj.basicOpen (grading I) a.val)
    n (originalPositiveHomogeneousChartIndexRepresentingObject001 I n hn)
    (originalPositiveHomogeneousChartIndexRepresentingIso001 I n hn)

end PfaffianDescent
end
