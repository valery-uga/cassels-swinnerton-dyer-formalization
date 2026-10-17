import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualTensorUnitAdjunct
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap_unit_right
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    schemeModuleTensorMap (𝟙 ((Scheme.Modules.pushforward f).obj M))
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f) ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f M
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.pushforward f).map (schemeModuleTensorUnitRightIso M).hom =
    (schemeModuleTensorUnitRightIso ((Scheme.Modules.pushforward f).obj M)).hom := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let G := Scheme.Modules.pushforward f
  let τ := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _
    ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom (𝟙 (G.obj M).val) τ.val) ≫
      (cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f M
        (SheafOfModules.unit X.ringCatSheaf) ≫
      G.map (schemeModuleTensorUnitRightIso M).hom)) = _
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap, adj, G,
    Equiv.apply_symm_apply]
  rw [cubicClosedPointSerreFiniteZeroResidual_tensorUnitRightIso_adjunct]
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
  | add z w hz hw => simp only [map_add]; rw [hz,hw]
  | tmul m r =>
    let W := op (f ⁻¹ᵁ U.unop)
    let m' : M.val.obj W := m
    let T := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) M.val
      (SheafOfModules.unit X.ringCatSheaf).val
    let a := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    change (schemeModuleTensorUnitRightIso M).hom.val.app W
      ((a.unit.app T).app W (m' ⊗ₜ[X.sheaf.obj.obj W] f.app U.unop r)) =
      f.app U.unop r • m'
    exact cubicClosedPointSerreFiniteZeroResidual_tensorUnitRightIso_sheafification_tmul
      M W m' (f.app U.unop r)
end PfaffianDescent
