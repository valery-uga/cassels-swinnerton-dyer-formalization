import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveTwistUnit
import PfaffianDescent.SerreExtensionFoundation

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The literal positive-three twist is internally trivialized on the common chart,
for every actual module, including the actual eleven-point ideal. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveThreeTensorRestrictIso
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (M : (scheme I).Modules) :
    (Scheme.Modules.restrictFunctor
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).obj
      (schemeModuleTensor M (positiveSheafOfModules (grading I) 3)) ≅
    (Scheme.Modules.restrictFunctor
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).obj M :=
  schemeModuleTensorRestrictIsoOfLocalTrivialization _ M _
    (overFunctorIsoUnit_of_restrictIsoUnit _
      (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell))

/-- The actual tensor trivialization preserves the actual ideal inclusion square. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveThreeTensorRestrictIso_naturality
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {M N : (scheme I).Modules} (f : M ⟶ N) :
    (Scheme.Modules.restrictFunctor
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).map
        (schemeModuleTensorMap f (𝟙 (positiveSheafOfModules (grading I) 3))) ≫
      (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeTensorRestrictIso I ell N).hom =
    (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeTensorRestrictIso I ell M).hom ≫
      (Scheme.Modules.restrictFunctor
        (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).map f :=
  schemeModuleTensorRestrictIsoOfLocalTrivialization_naturality _ _ f

/-- The SAME actual closed ideal is retained after removing the native positive-three twist. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveThreeIdealRestrictIso
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i] :
    (Scheme.Modules.restrictFunctor
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).obj
      (closedImmersionIdealTwist i (positiveSheafOfModules (grading I) 3)) ≅
    (Scheme.Modules.restrictFunctor
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).obj
      (IdealSheafDataModule.closedImmersionModule i) :=
  cubicClosedPointSerreSurfaceJetCotangent_positiveThreeTensorRestrictIso I ell _

end PfaffianDescent
