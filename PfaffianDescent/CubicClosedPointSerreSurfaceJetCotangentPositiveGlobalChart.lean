import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveGlobalLift

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open TopologicalSpace
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual positive-three quotient is supported on the common linear chart;
restriction there detects its zero morphisms without an external support certificate. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveQuotientChartUnit_isIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {Z : Scheme.{u}}
    (j : Z ⟶ (Proj.basicOpen (grading I) (ell : CoordinateRing I) : Scheme))
    [IsClosedImmersion (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)] :
    IsIso ((Scheme.Modules.restrictAdjunction
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).unit.app
      (closedImmersionIdealTwistSequence
        (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)
        (positiveSheafOfModules (grading I) 3)).X₃) := by
  apply closedImmersionIdealTwistTarget_restrictAdjunctionUnit_isIso
    _ j _ (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell)
    (quotientCoordinateOpenLifted I)
  · rw [Opens.coversTop_iff]
    exact quotientCoordinateOpenLifted_iSup I
  · intro a
    exact overFunctorIsoUnit_of_restrictIsoUnit (quotientCoordinateOpen I a.down)
      (quotientCoordinatePositiveTwistUnitIso_all I a.down 3)

/-- An actual global positive-three section whose quotient vanishes on the
common chart has a unique lift to the SAME actual global ideal twist. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveIdealGlobalLift_of_chart
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {Z : Scheme.{u}}
    (j : Z ⟶ (Proj.basicOpen (grading I) (ell : CoordinateRing I) : Scheme))
    [IsClosedImmersion (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)]
    (s : SheafOfModules.unit (scheme I).ringCatSheaf ⟶
      positiveSheafOfModules (grading I) 3)
    (hs : (Scheme.Modules.restrictFunctor
        (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).map
      (s ≫ (schemeModuleTensorUnitLeftIso
          (positiveSheafOfModules (grading I) 3)).inv ≫
        (closedImmersionIdealTwistSequence
          (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)
          (positiveSheafOfModules (grading I) 3)).g) = 0) :
    ∃! t : SheafOfModules.unit (scheme I).ringCatSheaf ⟶
        closedImmersionIdealTwist
          (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)
          (positiveSheafOfModules (grading I) 3),
      t ≫ cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion I
        (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι) = s := by
  letI := cubicClosedPointSerreSurfaceJetCotangent_positiveQuotientChartUnit_isIso I ell j
  apply cubicClosedPointSerreSurfaceJetCotangent_positiveIdealGlobalLift
  exact cubicClosedPointSerreSurfaceJetCotangent_eq_zero_of_restrict _ _ hs

end PfaffianDescent
