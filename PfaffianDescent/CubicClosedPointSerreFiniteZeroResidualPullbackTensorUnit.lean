import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPullbackTensorNaturality
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPushforwardTensorUnit
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualTensorRightUnitorNaturality
import PfaffianDescent.BundleSectionZeroLocus
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_unit_right
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f M
      (SheafOfModules.unit Y.ringCatSheaf) ≫
    schemeModuleTensorMap (𝟙 ((Scheme.Modules.pullback f).obj M))
      (BundleSectionZeroLocus.pullbackUnitComparison f) ≫
      (schemeModuleTensorUnitRightIso ((Scheme.Modules.pullback f).obj M)).hom =
    (Scheme.Modules.pullback f).map (schemeModuleTensorUnitRightIso M).hom := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  let P := Scheme.Modules.pullback f
  let G := Scheme.Modules.pushforward f
  let OY : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let u := BundleSectionZeroLocus.pullbackUnitComparison f
  let τ := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f
  have hτ : adj.unit.app OY ≫ G.map u = τ := by
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom
  have hρ : adj.homEquiv _ _ (P.map (schemeModuleTensorUnitRightIso M).hom) =
      (schemeModuleTensorUnitRightIso M).hom ≫ adj.unit.app M := by
    change adj.unit.app (schemeModuleTensor M OY) ≫
      G.map (P.map (schemeModuleTensorUnitRightIso M).hom) = _
    exact (adj.unit.naturality (schemeModuleTensorUnitRightIso M).hom).symm
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, hρ]
  simp only [cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap, adj, P, G,
    Equiv.apply_symm_apply]
  change (schemeModuleTensorMap (adj.unit.app M) (adj.unit.app OY) ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f (P.obj M) (P.obj OY)) ≫
    G.map (schemeModuleTensorMap (𝟙 (P.obj M)) u ≫
      (schemeModuleTensorUnitRightIso (P.obj M)).hom) =
    (schemeModuleTensorUnitRightIso M).hom ≫ adj.unit.app M
  rw [G.map_comp, Category.assoc, ← Category.assoc
    (cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f (P.obj M) (P.obj OY))]
  have hnat := cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap_naturality
    f (𝟙 (P.obj M)) u
  rw [← hnat]
  rw [G.map_id]
  have hcomb : schemeModuleTensorMap (adj.unit.app M) (adj.unit.app OY) ≫
      schemeModuleTensorMap (𝟙 (G.obj (P.obj M))) (G.map u) =
      schemeModuleTensorMap (adj.unit.app M) τ := by
    rw [schemeModuleTensorMap_comp]
    exact congrArg₂ schemeModuleTensorMap (Category.comp_id (adj.unit.app M)) hτ
  have hcomb' := congrArg (fun q => q ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f (P.obj M) OX ≫
        G.map (schemeModuleTensorUnitRightIso (P.obj M)).hom) hcomb
  simp only [Category.assoc] at hcomb'
  apply hcomb'.trans
  have hsplit : schemeModuleTensorMap (adj.unit.app M) τ =
      schemeModuleTensorMap (adj.unit.app M) (𝟙 OY) ≫
        schemeModuleTensorMap (𝟙 (G.obj (P.obj M))) τ := by
    rw [schemeModuleTensorMap_comp]
    exact (congrArg₂ schemeModuleTensorMap (Category.comp_id (adj.unit.app M))
      (Category.id_comp τ)).symm
  rw [hsplit, Category.assoc]
  have hunit := cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap_unit_right f (P.obj M)
  have hunit' := congrArg (fun q => schemeModuleTensorMap (adj.unit.app M) (𝟙 OY) ≫ q) hunit
  apply hunit'.trans
  exact cubicClosedPointSerreFiniteZeroResidual_tensorUnitRightIso_naturality (adj.unit.app M)
end PfaffianDescent
