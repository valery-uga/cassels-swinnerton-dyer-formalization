import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealTwist
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentFiber

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- Literal pullback along a point in an open agrees with pulling back the actual restriction. -/
def cubicClosedPointSerreSurfaceJetCotangent_pointRestrictPullbackIso
    {X Y : Scheme.{u}} (U : X.Opens) (j : Y ⟶ (U : Scheme)) (M : X.Modules) :
    (Scheme.Modules.pullback (j ≫ U.ι)).obj M ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.restrictFunctor U.ι).obj M) :=
  ((Scheme.Modules.pullbackComp j U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback j).mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm

/-- Removing the actual positive-three twist at an actual point preserves the SAME actual ideal. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveThreeIdealPointPullbackIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {Z Y : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    (j : Y ⟶ (Proj.basicOpen (grading I) (ell : CoordinateRing I) : Scheme)) :
    (Scheme.Modules.pullback (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)).obj
      (closedImmersionIdealTwist i (positiveSheafOfModules (grading I) 3)) ≅
    (Scheme.Modules.pullback (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)).obj
      (IdealSheafDataModule.closedImmersionModule i) :=
  cubicClosedPointSerreSurfaceJetCotangent_pointRestrictPullbackIso _ j _ ≪≫
    (Scheme.Modules.pullback j).mapIso
      (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeIdealRestrictIso I ell i) ≪≫
    (cubicClosedPointSerreSurfaceJetCotangent_pointRestrictPullbackIso _ j _).symm

/-- Actual Gamma of the point pullback of I(+3) is identified with actual Gamma of the
point pullback of I using the internally proved common-chart unit. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveThreeIdealPointGammaEquiv
    {K F : Type u} [Field K] [Field F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    (j : Spec (CommRingCat.of F) ⟶
      (Proj.basicOpen (grading I) (ell : CoordinateRing I) : Scheme)) :
    (moduleSpecΓFunctor (R := CommRingCat.of F)).obj
      ((Scheme.Modules.pullback (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)).obj
        (closedImmersionIdealTwist i (positiveSheafOfModules (grading I) 3))) ≃ₗ[F]
    (moduleSpecΓFunctor (R := CommRingCat.of F)).obj
      ((Scheme.Modules.pullback (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)).obj
        (IdealSheafDataModule.closedImmersionModule i)) :=
  ((moduleSpecΓFunctor (R := CommRingCat.of F)).mapIso
    (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeIdealPointPullbackIso I ell i j)).toLinearEquiv

end PfaffianDescent
