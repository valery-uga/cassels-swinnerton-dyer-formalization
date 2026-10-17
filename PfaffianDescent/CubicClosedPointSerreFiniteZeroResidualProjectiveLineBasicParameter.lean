import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualBasicParameterInsideOpen
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualProjectiveLineParameter

noncomputable section
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

instance cubicClosedPointSerreFiniteZeroResidual_projectiveLine_chart_domain
    (K : Type u) [Field K] (b : Bool) :
    IsDomain (ChartRing (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K)) b) := by
  let e := lineGrassmannianProjChartRingEquiv K b
  exact e.symm.toMulEquiv.isDomain

end PfaffianDescent
