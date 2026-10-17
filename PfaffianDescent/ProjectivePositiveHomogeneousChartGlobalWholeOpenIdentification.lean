import PfaffianDescent.ProjectiveChartGlobalUniversalWholeFamily
import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterSchemeGlueData
import PfaffianDescent.NativeWholeFiniteFamilyOpenLocusCartesianBaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- A genuine Cartesian square identifies the entire inverse image of a
chart range with the actual range of its first projection. -/
private theorem actualCartesianChartRangePreimage001
    {P X Y Z : Scheme.{u}} {i : P ⟶ X} {t : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback i t f g) :
    f ⁻¹' Set.range g = Set.range i := by
  simpa only [Set.preimage_univ, Set.image_univ] using
    (Scheme.image_preimage_eq_of_isPullback h.flip (Set.univ : Set Y)).symm

variable {J : Type u} {X B : Scheme.{u}} (F : X ⟶ B) (U : J → X.Opens) (n : ℕ)
variable [IsSeparated F] (H : J → Over B)
variable (eta : ∀ i, relativeFiniteFlatHilbertFunctor197 ((U i).ι ≫ F) n ≅ yoneda.obj (H i))

/-- Local instance is DERIVED from the actual native gluing datum before
chart-range types are formed; no openness hypothesis is added. -/
private theorem actualConstructedParameterChartIsOpenImmersion001 (i : J) :
    IsOpenImmersion ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι i) :=
  Scheme.GlueData.ι_isOpenImmersion
    (relativeOpenChartParameterSchemeGlueData001 F U n H eta) i

attribute [local instance] actualConstructedParameterChartIsOpenImmersion001

/-- The actual glued chart intersection pulls back to the SAME original
whole-family overlap, derived from the constructed native Cartesian pair. -/
theorem relativeOpenChartParameterGluedChartRange_preimage001 (i j : J) :
    (relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι i ⁻¹ᵁ
      ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι j).opensRange =
        relativeOpenChartParameterOverlap001 F (U i) (U j) n (H i) (eta i) := by
  apply TopologicalSpace.Opens.ext
  have h := actualCartesianChartRangePreimage001
    (relativeOpenChartParameterGlued_pairCartesian001 F U n H eta i j)
  change (relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι i ⁻¹'
    Set.range ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι j) = _
  exact h.trans (relativeOpenChartParameterOverlap001 F (U i) (U j) n (H i) (eta i)).range_ι

/-- The actual global universal WHOLE family defines its entire-source
containment locus in each original chart, with nilpotents retained. -/
def relativeOpenChartParameterUniversalWholeChartLocus001 (j : J) :
    (relativeOpenChartParameterGluedScheme001 F U n H eta).Opens :=
  finiteFamilyWholeOpenLocus314
    (relativeHilbertFamily197 F (relativeOpenChartParameterGluedObject001 F U n H eta)) n
    (relativeOpenChartParameterGlobalUniversalFamily001 F U n H eta)
    (pullback.snd (relativeOpenChartParameterGluedObject001 F U n H eta).hom F ⁻¹ᵁ U j)

/-- Arbitrary whole-family base change and the exact universal chart
restriction derive the original overlap on every constructed chart. -/
theorem relativeOpenChartParameterUniversalWholeChartLocus_preimage001 (i j : J) :
    (relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι i ⁻¹ᵁ
      relativeOpenChartParameterUniversalWholeChartLocus001 F U n H eta j =
        relativeOpenChartParameterOverlap001 F (U i) (U j) n (H i) (eta i) := by
  have h := relativeFiniteFlatHilbertWholeOpenLocus_baseChange001 F n (U j)
    (relativeOpenChartParameterGluedChartInclusionOver001 F U n H eta i)
    (relativeOpenChartParameterGlobalUniversalFamily001 F U n H eta)
  rw [relativeOpenChartParameterGlobalUniversalFamily_chart001] at h
  exact h.symm

/-- The actual parameter chart is EXACTLY the open on which the global
universal whole family lies in its original chart. No open identification
or matching outcome is supplied as a premise. -/
theorem relativeOpenChartParameterUniversalWholeChartLocus_eq_chartRange001 (j : J) :
    relativeOpenChartParameterUniversalWholeChartLocus001 F U n H eta j =
      ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι j).opensRange := by
  apply TopologicalSpace.Opens.ext
  ext x
  obtain ⟨i, y, rfl⟩ :=
    (relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι_jointly_surjective x
  have h :
      (relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι i ⁻¹ᵁ
        relativeOpenChartParameterUniversalWholeChartLocus001 F U n H eta j =
      (relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι i ⁻¹ᵁ
        ((relativeOpenChartParameterSchemeGlueData001 F U n H eta).ι j).opensRange :=
    (relativeOpenChartParameterUniversalWholeChartLocus_preimage001 F U n H eta i j).trans
      (relativeOpenChartParameterGluedChartRange_preimage001 F U n H eta i j).symm
  exact (congrArg (fun O : (H i).left.Opens => y ∈ O) h).to_iff

/-- The original all-positive internally chosen gluing datum also has
its own derived local chart-open instance, preserving every model choice. -/
private theorem originalConstructedParameterChartIsOpenImmersion001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma R))
    (n : ℕ) (hn : 0 < n) (a : projectivePositiveHomogeneousChartIndex001 (grading I)) :
    IsOpenImmersion ((originalPositiveHomogeneousParameterSchemeGlueData001 I n hn).ι a) :=
  Scheme.GlueData.ι_isOpenImmersion
    (originalPositiveHomogeneousParameterSchemeGlueData001 I n hn) a

attribute [local instance] originalConstructedParameterChartIsOpenImmersion001

/-- ORIGINAL Noetherian homogeneous data constructs every chart model,
gluing map and global whole family internally. Its positive-chart parameter
open is exactly the global universal entire-source containment locus. -/
theorem originalPositiveHomogeneousParameterUniversalWholeChartLocus_eq_chartRange001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma R))
    (n : ℕ) (hn : 0 < n) (a : projectivePositiveHomogeneousChartIndex001 (grading I)) :
    finiteFamilyWholeOpenLocus314
      (relativeHilbertFamily197 (toBase I) (Over.mk (originalPositiveHomogeneousParameterGluedToBase001 I n hn))) n
      (originalPositiveHomogeneousParameterGlobalUniversalFamily001 I n hn)
      (pullback.snd (originalPositiveHomogeneousParameterGluedToBase001 I n hn) (toBase I) ⁻¹ᵁ
        Proj.basicOpen (grading I) a.val) =
      ((originalPositiveHomogeneousParameterSchemeGlueData001 I n hn).ι a).opensRange :=
  relativeOpenChartParameterUniversalWholeChartLocus_eq_chartRange001 (toBase I)
    (fun a : projectivePositiveHomogeneousChartIndex001 (grading I) => Proj.basicOpen (grading I) a.val)
    n (originalPositiveHomogeneousChartIndexRepresentingObject001 I n hn)
    (originalPositiveHomogeneousChartIndexRepresentingIso001 I n hn) a

end PfaffianDescent
end
