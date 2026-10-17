import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualTensorUnitAdjunct
/- SOURCE ONLY / UNVERIFIED. Actual left unit on actual sheafified pure tensors. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem actualTensorUnitLeftIso_sheafification_tmul
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opensᵒᵖ)
    (r : X.sheaf.obj.obj U) (m : M.val.obj U) :
    let T := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
      (SheafOfModules.unit X.ringCatSheaf).val M.val
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    (schemeModuleTensorUnitLeftIso M).hom.val.app U
      ((adj.unit.app T).app U (r ⊗ₜ[X.sheaf.obj.obj U] m)) = r • m := by
  let T := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj)
    (SheafOfModules.unit X.ringCatSheaf).val M.val
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h : adj.unit.app T ≫ (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
        (schemeModuleTensorUnitLeftIso M).hom =
      (schemeModuleTensorUnitLeftRawIso M).hom :=
    cubicClosedPointSerreFiniteZeroResidual_tensorUnitLeftIso_adjunct M
  have h' := congrArg (fun q => q.app U (r ⊗ₜ[X.sheaf.obj.obj U] m)) h
  change (schemeModuleTensorUnitLeftIso M).hom.val.app U
      ((adj.unit.app T).app U (r ⊗ₜ[X.sheaf.obj.obj U] m)) = r • m at h'
  exact h'
end PfaffianDescent
