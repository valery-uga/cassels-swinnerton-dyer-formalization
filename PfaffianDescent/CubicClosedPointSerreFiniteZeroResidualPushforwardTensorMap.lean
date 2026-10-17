import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualTensorRestrictionMap
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorPresheafMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : X.Modules) :
    PresheafOfModules.Monoidal.tensorObj (R := Y.sheaf.obj)
      ((Scheme.Modules.pushforward f).obj M).val
      ((Scheme.Modules.pushforward f).obj N).val ⟶
    ((Scheme.Modules.pushforward f).obj (schemeModuleTensor M N)).val := by
  let T := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) M.val N.val
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app T
  refine
    { app := fun U => ?_
      naturality := ?_ }
  · let W := op (f ⁻¹ᵁ U.unop)
    let φ := (f.app U.unop).hom
    let e := cubicClosedPointSerreFiniteZeroResidual_tensorRestrictionMap φ (M.val.obj W) (N.val.obj W)
    change ModuleCat.of (Y.sheaf.obj.obj U)
      ((ModuleCat.restrictScalars φ).obj (M.val.obj W) ⊗[Y.sheaf.obj.obj U]
        (ModuleCat.restrictScalars φ).obj (N.val.obj W)) ⟶
      (ModuleCat.restrictScalars φ).obj ((schemeModuleTensor M N).val.obj W)
    letI : Module (Y.sheaf.obj.obj U) ((schemeModuleTensor M N).val.obj W) :=
      Module.compHom ((schemeModuleTensor M N).val.obj W) φ
    exact ModuleCat.ofHom
      (((ModuleCat.restrictScalars φ).map (η.app W)).hom.comp e)
  · intro U V i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simp only [map_add]; rw [hz,hw]
    | tmul m n =>
      let j := (Opens.map f.base).op.map i
      change (η.app (op (f ⁻¹ᵁ V.unop)))
        (M.val.map j m ⊗ₜ[X.sheaf.obj.obj (op (f ⁻¹ᵁ V.unop))] N.val.map j n) =
        (schemeModuleTensor M N).val.map j
          ((η.app (op (f ⁻¹ᵁ U.unop)))
            (m ⊗ₜ[X.sheaf.obj.obj (op (f ⁻¹ᵁ U.unop))] n))
      have h := congrArg (fun a => a (m ⊗ₜ[X.sheaf.obj.obj (op (f ⁻¹ᵁ U.unop))] n))
        (η.naturality j)
      change (η.app (op (f ⁻¹ᵁ V.unop)))
        (M.val.map j m ⊗ₜ[X.sheaf.obj.obj (op (f ⁻¹ᵁ V.unop))] N.val.map j n) =
        (schemeModuleTensor M N).val.map j
          ((η.app (op (f ⁻¹ᵁ U.unop)))
            (m ⊗ₜ[X.sheaf.obj.obj (op (f ⁻¹ᵁ U.unop))] n)) at h
      exact h

def cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : X.Modules) :
    schemeModuleTensor ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N) ⟶
    (Scheme.Modules.pushforward f).obj (schemeModuleTensor M N) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).symm
    (cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorPresheafMap f M N)
end PfaffianDescent
