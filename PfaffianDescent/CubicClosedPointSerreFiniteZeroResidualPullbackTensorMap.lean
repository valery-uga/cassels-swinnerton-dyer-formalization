import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPushforwardTensorMap
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (schemeModuleTensor M N) ⟶
    schemeModuleTensor ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let P := Scheme.Modules.pullback f
  exact (adj.homEquiv _ _).symm
    (schemeModuleTensorMap (adj.unit.app M) (adj.unit.app N) ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f (P.obj M) (P.obj N))
end PfaffianDescent
