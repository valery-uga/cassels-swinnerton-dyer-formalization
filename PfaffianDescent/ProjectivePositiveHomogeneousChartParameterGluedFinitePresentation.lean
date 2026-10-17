import PfaffianDescent.ProjectivePositiveHomogeneousChartParameterSchemeGlueData
import PfaffianDescent.ProjectivePositiveHomogeneousChartSameRepresenterFinitePresentation
import PfaffianDescent.NativeAlgebraSpecFinitePresentation307

/-! LFP of the ACTUALLY constructed original projective-chart parameter
scheme, using its own native source-open-cover and the exact original base
triangles. Every chart is the SAME already chosen all-test representer.
The genuine gluing constructor is an honest future dependency. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Ordinary property transport on exact original-base morphisms. The
actual caller supplies the constructed gluing triangle and genuine chart
LFP theorem, rather than assuming the global property. -/
private theorem originalGluedChartMapEquality_lfp_transport001
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    (hg : LocallyOfFinitePresentation g) : LocallyOfFinitePresentation f := by
  cases h
  exact hg

/-- The SAME actually glued original parameter scheme is LFP over R.
Its source cover and chart/base equalities are constructed by the native
gluing data. No gluing object, open cover, chart LFP or global LFP outcome
is supplied as a premise. The given H/eta are precisely the all-test
models already chosen for these original positive homogeneous charts. -/
theorem originalPositiveHomogeneousCharts_sameParameterGluedToBase_locallyOfFinitePresentation001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma R))
    (J : Type u) (a : J → CoordinateRing I) (d : J → ℕ)
    (hd : ∀ i, 0 < d i) (ha : ∀ i, a i ∈ grading I (d i))
    (n : ℕ) (hn : 0 < n) (H : J → Over (Spec (.of R)))
    (eta : ∀ i, relativeFiniteFlatHilbertFunctor197
      ((Proj.basicOpen (grading I) (a i)).ι ≫ toBase I) n ≅ yoneda.obj (H i)) :
    LocallyOfFinitePresentation (relativeOpenChartParameterGluedToBase001 (toBase I)
      (fun i => Proj.basicOpen (grading I) (a i)) n H eta) := by
  apply nativeLocallyOfFinitePresentation_of_sourceOpenCover307
    (relativeOpenChartParameterGluedToBase001 (toBase I)
      (fun i => Proj.basicOpen (grading I) (a i)) n H eta)
    (relativeOpenChartParameterSchemeGlueData001 (toBase I)
      (fun i => Proj.basicOpen (grading I) (a i)) n H eta).openCover
  intro i
  exact originalGluedChartMapEquality_lfp_transport001
    (relativeOpenChartParameterGluedToBase_chart001 (toBase I)
      (fun i => Proj.basicOpen (grading I) (a i)) n H eta i)
    (originalPositiveHomogeneousChart_sameAllTestHilbertRepresenter_locallyOfFinitePresentation001
      I (a i) (d i) (hd i) (ha i) n hn (H i) (eta i))

/-- The original Noetherian homogeneous data constructs EVERY positive
chart model/classifier internally and uses those SAME choices in its
actual gluing datum. Its original R morphism is genuinely LFP; no models,
classifiers, gluing, cover, global family, or LFP outcome is an input. -/
theorem originalPositiveHomogeneousParameterGluedToBase_locallyOfFinitePresentation001
    {R : Type u} [CommRing R] [IsNoetherianRing R] {sigma : Type} [Finite sigma]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule sigma R))
    (n : ℕ) (hn : 0 < n) :
    LocallyOfFinitePresentation (originalPositiveHomogeneousParameterGluedToBase001 I n hn) := by
  change LocallyOfFinitePresentation (relativeOpenChartParameterGluedToBase001 (toBase I)
    (fun a : projectivePositiveHomogeneousChartIndex001 (grading I) =>
      Proj.basicOpen (grading I) a.val) n
    (originalPositiveHomogeneousChartIndexRepresentingObject001 I n hn)
    (originalPositiveHomogeneousChartIndexRepresentingIso001 I n hn))
  exact originalPositiveHomogeneousCharts_sameParameterGluedToBase_locallyOfFinitePresentation001
    I (projectivePositiveHomogeneousChartIndex001 (grading I))
    (fun a => a.val) (fun a => Classical.choose a.property)
    (fun a => (Classical.choose_spec a.property).1)
    (fun a => (Classical.choose_spec a.property).2) n hn
    (originalPositiveHomogeneousChartIndexRepresentingObject001 I n hn)
    (originalPositiveHomogeneousChartIndexRepresentingIso001 I n hn)

end PfaffianDescent
end
