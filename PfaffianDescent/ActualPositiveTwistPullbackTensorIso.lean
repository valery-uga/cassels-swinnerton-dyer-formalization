import PfaffianDescent.ActualPositiveTwistChartUnit
import PfaffianDescent.CubicClosedPointSerreTensorStalkUnitIso
import PfaffianDescent.CubicClosedPointSerreTensorStalkGeneratorIso

/- SOURCE ONLY / UNVERIFIED. Actual degree-m chart generators and literal
pullback tensor comparison, not an abstract invertible-module substitute. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem actualPositiveTwist_exists_generator
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (m : ℕ) (y : scheme I) :
    ∃ (U : (scheme I).Opens)
      (g : SheafOfModules.unit (scheme I).ringCatSheaf ⟶ positiveSheafOfModules (grading I) m),
      y ∈ U ∧ IsIso ((Scheme.Modules.restrictFunctor U.ι).map g) := by
  have hy : y ∈ ⨆ j : Fin 4, quotientCoordinateOpen I j := by
    rw [quotientCoordinateOpen_iSup]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
  refine ⟨quotientCoordinateOpen I j, actualPositiveTwistChartBasisInvHom I ell m, hj, ?_⟩
  change IsIso ((Scheme.Modules.restrictFunctor
    (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).map
      (actualPositiveTwistChartBasisInvHom I ell m))
  exact actualPositiveTwistChartBasisInvHom_isIso I ell m

theorem actualPositiveTwist_pullbackTensorMap_isIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {X : Scheme.{u}} (f : X ⟶ scheme I) (M : (scheme I).Modules) (m : ℕ) :
    IsIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
      (positiveSheafOfModules (grading I) m)) := by
  letI := cubicClosedPointSerreTensorStalk_pullbackTensorMap_unit_isIso f M
  apply cubicClosedPointSerreTensorStalk_pullbackTensorMap_isIso_of_generators
  intro x
  exact actualPositiveTwist_exists_generator I m (f x)

def actualPositiveTwistPullbackTensorIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {X : Scheme.{u}} (f : X ⟶ scheme I) (M : (scheme I).Modules) (m : ℕ) :
    (Scheme.Modules.pullback f).obj (schemeModuleTensor M (positiveSheafOfModules (grading I) m)) ≅
      schemeModuleTensor ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj (positiveSheafOfModules (grading I) m)) := by
  letI := actualPositiveTwist_pullbackTensorMap_isIso I f M m
  exact asIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
    (positiveSheafOfModules (grading I) m))

lemma actualPositiveTwistPullbackTensorIso_hom
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {X : Scheme.{u}} (f : X ⟶ scheme I) (M : (scheme I).Modules) (m : ℕ) :
    (actualPositiveTwistPullbackTensorIso I f M m).hom =
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
        (positiveSheafOfModules (grading I) m) := rfl

end PfaffianDescent
