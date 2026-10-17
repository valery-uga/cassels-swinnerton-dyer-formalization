import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveCubicKernelCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealChartSectionComparison

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual global cubic ideal lift restricts to the SAME native affine
ideal section h=q/ell³. -/
abbrev cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernel_chartSection
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {B : Type u} [CommRing B] (g : Away (grading I) (ell : CoordinateRing I) →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)]
    (q : grading I 3)
    (hq : g (Away.mk (grading I) ell.2 3 (q : CoordinateRing I)
      (by simpa using q.2)) = 0)
    (v : SheafOfModules.unit (scheme I).ringCatSheaf ⟶
      closedImmersionIdealTwist
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g)
        (positiveSheafOfModules (grading I) 3))
    (hv : v ≫ cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion I
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g) =
      (positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
        (positiveGlobalSectionOfHomogeneous (grading I) 3 q)) :=
  cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChart_sectionComparison
    (Proj.basicOpen (grading I) (ell : CoordinateRing I))
    (Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2 Nat.zero_lt_one).inv
    (positiveSheafOfModules (grading I) 3)
    (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell)
    (Spec.map (CommRingCat.ofHom g))
    ((positiveSheafOfModules (grading I) 3).unitHomEquiv.symm
      (positiveGlobalSectionOfHomogeneous (grading I) 3 q)) v hv
    (cubicClosedPointSerreSurfaceJetCotangent_nativeIdealSectionHom g
      ⟨Away.mk (grading I) ell.2 3 (q : CoordinateRing I) (by simpa using q.2), hq⟩)
    (cubicClosedPointSerreSurfaceJetCotangent_positiveCubicKernel_localCoefficient I ell g q hq)

end PfaffianDescent
