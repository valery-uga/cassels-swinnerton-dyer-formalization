import PfaffianDescent.CubicClosedPointSerreTensorStalkUnitIso
import PfaffianDescent.CubicClosedPointSerreTensorStalkGeneratorIso
import PfaffianDescent.CubicClosedPointSerreTensorStalkPositiveGenerators

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The SAME actual pullback tensor comparison is an isomorphism for the
native positive-three twist, with chart generators derived internally. -/
theorem cubicClosedPointSerreTensorStalk_pullbackTensorMap_positiveThree_isIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {X : Scheme.{u}} (f : X ⟶ scheme I) (M : (scheme I).Modules) :
    IsIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
      (positiveSheafOfModules (grading I) 3)) := by
  letI := cubicClosedPointSerreTensorStalk_pullbackTensorMap_unit_isIso f M
  apply cubicClosedPointSerreTensorStalk_pullbackTensorMap_isIso_of_generators
  intro x
  exact cubicClosedPointSerreTensorStalk_positiveThree_exists_generator I (f x)

/-- Actual positive-three tensor/pullback comparison with its literal native
comparison morphism as the hom. -/
def cubicClosedPointSerreTensorStalk_pullbackPositiveThreeTensorIso
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {X : Scheme.{u}} (f : X ⟶ scheme I) (M : (scheme I).Modules) :
    (Scheme.Modules.pullback f).obj
      (schemeModuleTensor M (positiveSheafOfModules (grading I) 3)) ≅
    schemeModuleTensor ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj (positiveSheafOfModules (grading I) 3)) := by
  letI := cubicClosedPointSerreTensorStalk_pullbackTensorMap_positiveThree_isIso I f M
  exact asIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
    (positiveSheafOfModules (grading I) 3))

theorem cubicClosedPointSerreTensorStalk_pullbackPositiveThreeTensorIso_hom
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    {X : Scheme.{u}} (f : X ⟶ scheme I) (M : (scheme I).Modules) :
    (cubicClosedPointSerreTensorStalk_pullbackPositiveThreeTensorIso I f M).hom =
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
        (positiveSheafOfModules (grading I) 3) := rfl

end PfaffianDescent
