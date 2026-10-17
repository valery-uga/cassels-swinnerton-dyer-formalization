import PfaffianDescent.ActualTensorUnitLeftPureTensor
/- SOURCE ONLY / UNVERIFIED. Actual pushforward tensor LEFT-unit compatibility. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem actualPushforwardTensorMap_unit_left
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules) :
    schemeModuleTensorMap (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f)
      (𝟙 ((Scheme.Modules.pushforward f).obj M)) ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f
        (SheafOfModules.unit X.ringCatSheaf) M ≫
      (Scheme.Modules.pushforward f).map (schemeModuleTensorUnitLeftIso M).hom =
    (schemeModuleTensorUnitLeftIso ((Scheme.Modules.pushforward f).obj M)).hom := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  let G := Scheme.Modules.pushforward f
  let τ := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _
    ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
      (PresheafOfModules.Monoidal.tensorHom τ.val (𝟙 (G.obj M).val)) ≫
      (cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f
        (SheafOfModules.unit X.ringCatSheaf) M ≫
      G.map (schemeModuleTensorUnitLeftIso M).hom)) = _
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap, adj, G,
    Equiv.apply_symm_apply]
  rw [cubicClosedPointSerreFiniteZeroResidual_tensorUnitLeftIso_adjunct]
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
  | add z w hz hw => simp only [map_add]; rw [hz,hw]
  | tmul r m =>
    let W := op (f ⁻¹ᵁ U.unop)
    let m' : M.val.obj W := m
    let T := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
      (SheafOfModules.unit X.ringCatSheaf).val M.val
    let a := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    change (schemeModuleTensorUnitLeftIso M).hom.val.app W
      ((a.unit.app T).app W (f.app U.unop r ⊗ₜ[X.sheaf.obj.obj W] m')) =
      f.app U.unop r • m'
    exact actualTensorUnitLeftIso_sheafification_tmul
      M W (f.app U.unop r) m'
end PfaffianDescent
