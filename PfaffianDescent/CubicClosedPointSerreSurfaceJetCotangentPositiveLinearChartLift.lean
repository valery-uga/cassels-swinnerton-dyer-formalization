import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealRefinedChartLocalKernel
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealLinearChart
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveGlobalChart

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- A literal preimage in the SAME ideal on Spec(Away ell) globalizes into
the actual positive-three ideal. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveLinearChart_globalLift
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {B : Type u} [CommRing B]
    (g : Away (grading I) (ell : CoordinateRing I) →+* B)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion ((Spec.map (CommRingCat.ofHom g) ≫
      (Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2
        Nat.zero_lt_one).inv) ≫
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)]
    (s : SheafOfModules.unit (scheme I).ringCatSheaf ⟶
      positiveSheafOfModules (grading I) 3)
    (t : SheafOfModules.unit
      (Spec (CommRingCat.of (Away (grading I) (ell : CoordinateRing I)))).ringCatSheaf ⟶
      closedImmersionModule (Spec.map (CommRingCat.ofHom g)))
    (ht : t ≫ closedImmersionModuleToUnit (Spec.map (CommRingCat.ofHom g)) =
      (Scheme.Modules.restrictUnitIso
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).inv ≫
      (Scheme.Modules.restrictFunctor
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell)).map s ≫
      (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeLinearChartUnitIso I ell).hom) :
    ∃! v : SheafOfModules.unit (scheme I).ringCatSheaf ⟶
      closedImmersionIdealTwist ((Spec.map (CommRingCat.ofHom g) ≫
        (Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2
          Nat.zero_lt_one).inv) ≫
        (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)
        (positiveSheafOfModules (grading I) 3),
      v ≫ cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion I
        ((Spec.map (CommRingCat.ofHom g) ≫
          (Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2
            Nat.zero_lt_one).inv) ≫
          (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι) = s := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  let e := Proj.basicOpenIsoSpec (grading I) (ell : CoordinateRing I) ell.2 Nat.zero_lt_one
  exact cubicClosedPointSerreSurfaceJetCotangent_positiveIdealGlobalLift_of_chart I ell
    (Spec.map (CommRingCat.ofHom g) ≫ e.inv) s
    (cubicClosedPointSerreSurfaceJetCotangent_restrictCompositeIso_reflect_zero U e.symm _
      (cubicClosedPointSerreSurfaceJetCotangent_refinedIdealChart_localKernel U e.inv
        (positiveSheafOfModules (grading I) 3)
        (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell)
        (Spec.map (CommRingCat.ofHom g)) s t ht))

end PfaffianDescent
