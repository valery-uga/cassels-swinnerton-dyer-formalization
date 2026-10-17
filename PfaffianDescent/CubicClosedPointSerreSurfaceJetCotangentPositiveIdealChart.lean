import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveIdealChartAbstract
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveGlobalLift

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The discrepancy of the two ACTUAL native positive-three chart coordinates. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveChartUnitDiscrepancy
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1) :
    SheafOfModules.unit (Proj.basicOpen (grading I) (ell : CoordinateRing I) : Scheme).ringCatSheaf ≅
      SheafOfModules.unit (Proj.basicOpen (grading I) (ell : CoordinateRing I) : Scheme).ringCatSheaf :=
  cubicClosedPointSerreSurfaceJetCotangent_abstractChartUnitDiscrepancy
    (Proj.basicOpen (grading I) (ell : CoordinateRing I))
    (positiveSheafOfModules (grading I) 3)
    (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell)

/-- Native inclusion-compatible coordinates on the SAME actual positive ideal. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveIdealChartIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {Z : Scheme.{u}}
    (j : Z ⟶ (Proj.basicOpen (grading I) (ell : CoordinateRing I) : Scheme))
    [IsClosedImmersion j]
    [IsClosedImmersion (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)] :
    (Scheme.Modules.restrictFunctor
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).obj
      (closedImmersionIdealTwist
        (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)
        (positiveSheafOfModules (grading I) 3)) ≅ closedImmersionModule j :=
  cubicClosedPointSerreSurfaceJetCotangent_abstractIdealChartIso
    (Proj.basicOpen (grading I) (ell : CoordinateRing I))
    (positiveSheafOfModules (grading I) 3)
    (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell) j

/-- The literal actual positive ideal inclusion becomes the native unit
coordinate map. The local unit and all ideal comparisons are constructed internally. -/
abbrev cubicClosedPointSerreSurfaceJetCotangent_positiveIdealChartIso_toUnit
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {Z : Scheme.{u}}
    (j : Z ⟶ (Proj.basicOpen (grading I) (ell : CoordinateRing I) : Scheme))
    [IsClosedImmersion j]
    [IsClosedImmersion (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)] :=
  cubicClosedPointSerreSurfaceJetCotangent_abstractIdealChartIso_toUnit
    (Proj.basicOpen (grading I) (ell : CoordinateRing I))
    (positiveSheafOfModules (grading I) 3)
    (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell) j

end PfaffianDescent
