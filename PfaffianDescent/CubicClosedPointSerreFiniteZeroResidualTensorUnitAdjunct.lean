import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPushforwardTensorMap
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_tensorUnitLeftIso_adjunct
    {X : Scheme.{u}} (M : X.Modules) :
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    adj.homEquiv _ _ (schemeModuleTensorUnitLeftIso M).hom =
      (schemeModuleTensorUnitLeftRawIso M).hom := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  change adj.homEquiv _ _
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (schemeModuleTensorUnitLeftRawIso M).hom ≫ adj.counit.app M) = _
  rw [adj.homEquiv_naturality_left]
  have h := schemeModuleSheafificationHomEquiv_counit_comp (𝟙 M)
  dsimp only at h
  have hc : adj.counit.app M ≫ 𝟙 M = adj.counit.app M := Category.comp_id _
  have h' : adj.homEquiv M.val M (adj.counit.app M) = 𝟙 M.val :=
    (congrArg (adj.homEquiv M.val M) hc).symm.trans h
  exact (congrArg ((schemeModuleTensorUnitLeftRawIso M).hom ≫ ·) h').trans
    (Category.comp_id _)
theorem cubicClosedPointSerreFiniteZeroResidual_tensorUnitRightIso_adjunct
    {X : Scheme.{u}} (M : X.Modules) :
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    adj.homEquiv _ _ (schemeModuleTensorUnitRightIso M).hom =
      (schemeModuleTensorUnitRightRawIso M).hom := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  change adj.homEquiv _ _
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (schemeModuleTensorUnitRightRawIso M).hom ≫ adj.counit.app M) = _
  rw [adj.homEquiv_naturality_left]
  have h := schemeModuleSheafificationHomEquiv_counit_comp (𝟙 M)
  dsimp only at h
  have hc : adj.counit.app M ≫ 𝟙 M = adj.counit.app M := Category.comp_id _
  have h' : adj.homEquiv M.val M (adj.counit.app M) = 𝟙 M.val :=
    (congrArg (adj.homEquiv M.val M) hc).symm.trans h
  exact (congrArg ((schemeModuleTensorUnitRightRawIso M).hom ≫ ·) h').trans
    (Category.comp_id _)
theorem cubicClosedPointSerreFiniteZeroResidual_tensorUnitRightIso_sheafification_tmul
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opensᵒᵖ)
    (m : M.val.obj U) (r : X.sheaf.obj.obj U) :
    let T := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) M.val
      (SheafOfModules.unit X.ringCatSheaf).val
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    (schemeModuleTensorUnitRightIso M).hom.val.app U
      ((adj.unit.app T).app U (m ⊗ₜ[X.sheaf.obj.obj U] r)) = r • m := by
  let T := PresheafOfModules.Monoidal.tensorObj (R := X.sheaf.obj) M.val
    (SheafOfModules.unit X.ringCatSheaf).val
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h : adj.unit.app T ≫ (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map (schemeModuleTensorUnitRightIso M).hom =
      (schemeModuleTensorUnitRightRawIso M).hom :=
    cubicClosedPointSerreFiniteZeroResidual_tensorUnitRightIso_adjunct M
  have h' := congrArg (fun q => q.app U (m ⊗ₜ[X.sheaf.obj.obj U] r)) h
  change (schemeModuleTensorUnitRightIso M).hom.val.app U
      ((adj.unit.app T).app U (m ⊗ₜ[X.sheaf.obj.obj U] r)) = r • m at h'
  exact h'

end PfaffianDescent
