import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPullbackTensorUnit

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- The literal actual pullback tensor comparison is an isomorphism when
the right factor is the actual structure sheaf. -/
theorem cubicClosedPointSerreTensorStalk_pullbackTensorMap_unit_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    IsIso (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
      (SheafOfModules.unit Y.ringCatSheaf)) := by
  let P := Scheme.Modules.pullback f
  let u := pullbackUnitComparison f
  letI : IsIso u := isIso_pullbackUnitComparison f
  let e := schemeModuleTensorMapIso (Iso.refl (P.obj M)) (asIso u)
  let r := schemeModuleTensorUnitRightIso (P.obj M)
  let c := cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
    (SheafOfModules.unit Y.ringCatSheaf)
  letI : IsIso (c ≫ e.hom ≫ r.hom) := by
    change IsIso (c ≫ schemeModuleTensorMap (𝟙 (P.obj M)) u ≫ r.hom)
    rw [cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_unit_right]
    infer_instance
  exact IsIso.of_isIso_comp_right c (e.hom ≫ r.hom)

end PfaffianDescent
