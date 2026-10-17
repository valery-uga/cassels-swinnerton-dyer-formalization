import PfaffianDescent.ActualModuleLocalTensorSection
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPullbackTensorMap

/- SOURCE ONLY / UNVERIFIED. The installed actual tensor/pushforward
map acts on literal local pure tensors by the true target tensor section,
derived from its sheafification adjunction and actual scalar restriction. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma actualPushforwardTensorMap_localSection {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M N : X.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (n : N.val.obj (op (f ⁻¹ᵁ U))) :
    (cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f M N).val.app (op U)
      (actualModuleLocalTensorSection
        ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) U m n) =
    actualModuleLocalTensorSection M N (f ⁻¹ᵁ U) m n := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let A := PresheafOfModules.Monoidal.tensorObj
    ((Scheme.Modules.pushforward f).obj M).val ((Scheme.Modules.pushforward f).obj N).val
  let p := cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorPresheafMap f M N
  have h := (adj.homEquiv A
    ((Scheme.Modules.pushforward f).obj (schemeModuleTensor M N))).apply_symm_apply p
  rw [Adjunction.homEquiv_unit] at h
  have hz := congrArg (fun v => v.app (op U) (m ⊗ₜ[Γ(Y, U)] n)) h
  change (cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f M N).val.app (op U)
      (actualModuleLocalTensorSection
        ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) U m n) =
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (PresheafOfModules.Monoidal.tensorObj M.val N.val)).app (op (f ⁻¹ᵁ U))
      (cubicClosedPointSerreFiniteZeroResidual_tensorRestrictionMap (f.app U).hom
        (M.val.obj (op (f ⁻¹ᵁ U))) (N.val.obj (op (f ⁻¹ᵁ U)))
        (m ⊗ₜ[Γ(Y, U)] n)) at hz
  exact hz

end PfaffianDescent
