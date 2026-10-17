import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveTwistUnit

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- At every actual point, a native homogeneous coordinate cube supplies
an actual global unit map generating the positive-three twist on its chart. -/
theorem cubicClosedPointSerreTensorStalk_positiveThree_exists_generator
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (y : scheme I) :
    ∃ (U : (scheme I).Opens)
      (g : SheafOfModules.unit (scheme I).ringCatSheaf ⟶ positiveSheafOfModules (grading I) 3),
      y ∈ U ∧ IsIso ((Scheme.Modules.restrictFunctor U.ι).map g) := by
  have hy : y ∈ ⨆ j : Fin 4, quotientCoordinateOpen I j := by
    rw [quotientCoordinateOpen_iSup]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
  refine ⟨quotientCoordinateOpen I j,
    cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom I ell, hj, ?_⟩
  change IsIso ((Scheme.Modules.restrictFunctor
    (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).map
    (cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom I ell))
  exact cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom_isIso I ell

end PfaffianDescent
