import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealChart
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentLinearChartIdeal

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The native positive-three unit coordinate on the LITERAL Spec(Away ell) chart. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveThreeLinearChartUnitIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1) :
    (Scheme.Modules.restrictFunctor
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).obj
      (positiveSheafOfModules (grading I) 3) ≅
    SheafOfModules.unit (Spec (CommRingCat.of (Away (grading I) (ell : CoordinateRing I)))).ringCatSheaf := by
  let e := Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2 Nat.zero_lt_one
  exact (Scheme.Modules.restrictFunctorComp e.inv _).app _ ≪≫
    (Scheme.Modules.restrictFunctor e.inv).mapIso
      (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell) ≪≫
    Scheme.Modules.restrictUnitIso e.inv

/-- Actual positive ideal coordinates on the literal affine chart map Spec(g),
with no replacement of the original closed-point ideal. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveIdealLinearChartIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {B : Type u} [CommRing B]
    (g : Away (grading I) (ell : CoordinateRing I) →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion ((Spec.map (CommRingCat.ofHom g) ≫
      (Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2
        Nat.zero_lt_one).inv) ≫
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)] :
    (Scheme.Modules.restrictFunctor
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).obj
      (closedImmersionIdealTwist ((Spec.map (CommRingCat.ofHom g) ≫
        (Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2
          Nat.zero_lt_one).inv) ≫
        (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)
        (positiveSheafOfModules (grading I) 3)) ≅
      closedImmersionModule (Spec.map (CommRingCat.ofHom g)) := by
  let e := Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2 Nat.zero_lt_one
  let j := Spec.map (CommRingCat.ofHom g) ≫ e.inv
  exact (Scheme.Modules.restrictFunctorComp e.inv _).app _ ≪≫
    (Scheme.Modules.restrictFunctor e.inv).mapIso
      (cubicClosedPointSerreSurfaceJetCotangent_positiveIdealChartIso I ell j) ≪≫
    cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso e.inv
      (Spec.map (CommRingCat.ofHom g))

end PfaffianDescent
