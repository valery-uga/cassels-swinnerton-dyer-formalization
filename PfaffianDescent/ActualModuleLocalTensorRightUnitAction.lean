import PfaffianDescent.ActualModuleLocalTensorSection
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualTensorUnitAdjunct

/- SOURCE ONLY / UNVERIFIED. The actual tensor right-unit map contracts
LOCAL pure tensors to their literal coefficient times the original section,
using the actual sheafification triangle identity. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma actualModuleLocalTensorRightUnitAction {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (r : Γ(X, U)) :
    (schemeModuleTensorUnitRightIso M).hom.val.app (op U)
      (actualModuleLocalTensorSection M (SheafOfModules.unit X.ringCatSheaf) U m r) =
        r • m := by
  exact cubicClosedPointSerreFiniteZeroResidual_tensorUnitRightIso_sheafification_tmul
    M (op U) m r

end PfaffianDescent
