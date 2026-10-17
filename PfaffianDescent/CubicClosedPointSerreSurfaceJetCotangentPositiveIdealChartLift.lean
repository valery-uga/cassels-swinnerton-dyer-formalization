import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealChartLocalKernel
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveGlobalChart

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist IdealSheafDataModule
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- A literal local ideal preimage of the positive-section coefficient
globalizes to the actual positive ideal. This is the kernel-lift adapter
used after the native affine H section has been constructed. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveIdealChartIso_globalLift
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    {Z : Scheme.{u}}
    (j : Z ⟶ (Proj.basicOpen (grading I) (ell : CoordinateRing I) : Scheme))
    [IsClosedImmersion j]
    [IsClosedImmersion (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)]
    (s : SheafOfModules.unit (scheme I).ringCatSheaf ⟶
      positiveSheafOfModules (grading I) 3)
    (t : SheafOfModules.unit
        (Proj.basicOpen (grading I) (ell : CoordinateRing I) : Scheme).ringCatSheaf ⟶
      closedImmersionModule j)
    (ht : t ≫ closedImmersionModuleToUnit j =
      (Scheme.Modules.restrictUnitIso
        (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).inv ≫
      (Scheme.Modules.restrictFunctor
        (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).map s ≫
      (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell).hom) :
    ∃! v : SheafOfModules.unit (scheme I).ringCatSheaf ⟶
        closedImmersionIdealTwist
          (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι)
          (positiveSheafOfModules (grading I) 3),
      v ≫ cubicClosedPointSerreSurfaceJetCotangent_positiveIdealInclusion I
        (j ≫ (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι) = s := by
  exact cubicClosedPointSerreSurfaceJetCotangent_positiveIdealGlobalLift_of_chart I ell j s
    (cubicClosedPointSerreSurfaceJetCotangent_abstractIdealChart_localKernel
      (Proj.basicOpen (grading I) (ell : CoordinateRing I))
      (positiveSheafOfModules (grading I) 3)
      (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell) j s t ht)

end PfaffianDescent
