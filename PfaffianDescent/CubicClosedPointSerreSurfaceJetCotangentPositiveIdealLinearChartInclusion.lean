import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealLinearChart
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealChartRefinement

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The literal Spec(Away ell) positive ideal coordinate commutes with the
actual positive ideal inclusion. -/
abbrev cubicClosedPointSerreSurfaceJetCotangent_positiveIdealLinearChartIso_toUnit
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {B : Type u} [CommRing B]
    (g : Away (grading I) (ell : CoordinateRing I) →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion ((Spec.map (CommRingCat.ofHom g) ≫
      (Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2
        Nat.zero_lt_one).inv) ≫
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)] :=
  cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChartIso_toUnit
    (Proj.basicOpen (grading I) (ell : CoordinateRing I))
    (Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2 Nat.zero_lt_one).inv
    (positiveSheafOfModules (grading I) 3)
    (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell)
    (Spec.map (CommRingCat.ofHom g))

end PfaffianDescent
