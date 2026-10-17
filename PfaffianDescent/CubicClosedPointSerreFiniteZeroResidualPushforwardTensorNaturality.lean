import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPushforwardTensorMap
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorPresheafMap_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M M' N N' : X.Modules}
    (a : M ⟶ M') (b : N ⟶ N') :
    PresheafOfModules.Monoidal.tensorHom
      ((Scheme.Modules.pushforward f).map a).val ((Scheme.Modules.pushforward f).map b).val ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorPresheafMap f M' N' =
    cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorPresheafMap f M N ≫
      ((Scheme.Modules.pushforward f).map (schemeModuleTensorMap a b)).val := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let T := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) M.val N.val
  let T' := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) M'.val N'.val
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add]; rw [hz,hw]
  | tmul m n =>
    let W := op (f ⁻¹ᵁ U.unop)
    change (adj.unit.app T').app W
      (a.val.app W m ⊗ₜ[X.sheaf.obj.obj W] b.val.app W n) =
      (schemeModuleTensorMap a b).val.app W
        ((adj.unit.app T).app W (m ⊗ₜ[X.sheaf.obj.obj W] n))
    have h := congrArg (fun q => q.app W (m ⊗ₜ[X.sheaf.obj.obj W] n))
      (adj.unit.naturality (PresheafOfModules.Monoidal.tensorHom a.val b.val))
    change (adj.unit.app T').app W
      (a.val.app W m ⊗ₜ[X.sheaf.obj.obj W] b.val.app W n) =
      (schemeModuleTensorMap a b).val.app W
        ((adj.unit.app T).app W (m ⊗ₜ[X.sheaf.obj.obj W] n)) at h
    exact h

theorem cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y) {M M' N N' : X.Modules}
    (a : M ⟶ M') (b : N ⟶ N') :
    schemeModuleTensorMap ((Scheme.Modules.pushforward f).map a)
      ((Scheme.Modules.pushforward f).map b) ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f M' N' =
    cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f M N ≫
      (Scheme.Modules.pushforward f).map (schemeModuleTensorMap a b) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _
    ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom
        ((Scheme.Modules.pushforward f).map a).val ((Scheme.Modules.pushforward f).map b).val) ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f M' N') = _
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap,
    adj, Equiv.apply_symm_apply]
  exact cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorPresheafMap_naturality f a b
end PfaffianDescent
