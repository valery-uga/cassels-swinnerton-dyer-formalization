import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPullbackTensorNaturality
import PfaffianDescent.ActualPushforwardTensorLeftUnit
/- SOURCE ONLY / UNVERIFIED. Actual pullback tensor LEFT-unit compatibility. -/
import PfaffianDescent.BundleSectionZeroLocus
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem actualPullbackTensorMap_unit_left
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap f
      (SheafOfModules.unit Y.ringCatSheaf) M ≫
    schemeModuleTensorMap (BundleSectionZeroLocus.pullbackUnitComparison f)
      (𝟙 ((Scheme.Modules.pullback f).obj M)) ≫
      (schemeModuleTensorUnitLeftIso ((Scheme.Modules.pullback f).obj M)).hom =
    (Scheme.Modules.pullback f).map (schemeModuleTensorUnitLeftIso M).hom := by
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
  have hρ : adj.homEquiv _ _ (P.map (schemeModuleTensorUnitLeftIso M).hom) =
      (schemeModuleTensorUnitLeftIso M).hom ≫ adj.unit.app M := by
    change adj.unit.app (schemeModuleTensor OY M) ≫
      G.map (P.map (schemeModuleTensorUnitLeftIso M).hom) = _
    exact (adj.unit.naturality (schemeModuleTensorUnitLeftIso M).hom).symm
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_naturality_right, hρ]
  simp only [cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap, adj, P, G,
    Equiv.apply_symm_apply]
  change (schemeModuleTensorMap (adj.unit.app OY) (adj.unit.app M) ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f (P.obj OY) (P.obj M)) ≫
    G.map (schemeModuleTensorMap u (𝟙 (P.obj M)) ≫
      (schemeModuleTensorUnitLeftIso (P.obj M)).hom) =
    (schemeModuleTensorUnitLeftIso M).hom ≫ adj.unit.app M
  rw [G.map_comp, Category.assoc, ← Category.assoc
    (cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f (P.obj OY) (P.obj M))]
  have hnat := cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap_naturality
    f u (𝟙 (P.obj M))
  rw [← hnat]
  rw [G.map_id]
  have hcomb : schemeModuleTensorMap (adj.unit.app OY) (adj.unit.app M) ≫
      schemeModuleTensorMap (G.map u) (𝟙 (G.obj (P.obj M))) =
      schemeModuleTensorMap τ (adj.unit.app M) := by
    rw [schemeModuleTensorMap_comp]
    exact congrArg₂ schemeModuleTensorMap hτ (Category.comp_id (adj.unit.app M))
  have hcomb' := congrArg (fun q => q ≫
      cubicClosedPointSerreFiniteZeroResidual_pushforwardTensorMap f OX (P.obj M) ≫
        G.map (schemeModuleTensorUnitLeftIso (P.obj M)).hom) hcomb
  simp only [Category.assoc] at hcomb'
  apply hcomb'.trans
  have hsplit : schemeModuleTensorMap τ (adj.unit.app M) =
      schemeModuleTensorMap (𝟙 OY) (adj.unit.app M) ≫
        schemeModuleTensorMap τ (𝟙 (G.obj (P.obj M))) := by
    rw [schemeModuleTensorMap_comp]
    exact (congrArg₂ schemeModuleTensorMap (Category.id_comp τ)
      (Category.comp_id (adj.unit.app M))).symm
  rw [hsplit, Category.assoc]
  have hunit := actualPushforwardTensorMap_unit_left f (P.obj M)
  have hunit' := congrArg (fun q => schemeModuleTensorMap (𝟙 OY) (adj.unit.app M) ≫ q) hunit
  apply hunit'.trans
  exact schemeModuleTensorUnitLeftIso_naturality (adj.unit.app M)
end PfaffianDescent
