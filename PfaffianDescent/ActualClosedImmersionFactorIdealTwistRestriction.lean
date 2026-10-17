import PfaffianDescent.ActualClosedImmersionFactorIdealRestriction
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPullbackTensorNaturality

/- SOURCE ONLY / UNVERIFIED. GENUINE ambient ideal-twist restriction to
its actual subscheme ideal, retaining the actual pullback of the ambient
line bundle. No ambient/cubic ideal substitution is made. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open BundleSectionZeroLocus IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

def actualClosedImmersionFactorIdealTwistRestriction
    {Y X Z : Scheme.{u}} (i : X ⟶ Y) (q : Z ⟶ X)
    [IsClosedImmersion q] [IsClosedImmersion (q ≫ i)] (T : Y.Modules) :
    (Scheme.Modules.pullback i).obj (schemeModuleTensor (closedImmersionModule (q ≫ i)) T) ⟶
      schemeModuleTensor (closedImmersionModule q) ((Scheme.Modules.pullback i).obj T) :=
  cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap i
      (closedImmersionModule (q ≫ i)) T ≫
    schemeModuleTensorMap (actualClosedImmersionFactorIdealRestriction i q)
      (𝟙 ((Scheme.Modules.pullback i).obj T))

lemma actualClosedImmersionFactorIdealTwistRestriction_toUnit
    {Y X Z : Scheme.{u}} (i : X ⟶ Y) (q : Z ⟶ X)
    [IsClosedImmersion q] [IsClosedImmersion (q ≫ i)] (T : Y.Modules) :
    actualClosedImmersionFactorIdealTwistRestriction i q T ≫
        schemeModuleTensorMap (closedImmersionModuleToUnit q)
          (𝟙 ((Scheme.Modules.pullback i).obj T)) =
      (Scheme.Modules.pullback i).map
        (schemeModuleTensorMap (closedImmersionModuleToUnit (q ≫ i)) (𝟙 T)) ≫
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap i (schemeModuleUnit Y) T ≫
      schemeModuleTensorMap (pullbackUnitComparison i)
        (𝟙 ((Scheme.Modules.pullback i).obj T)) := by
  unfold actualClosedImmersionFactorIdealTwistRestriction
  rw [Category.assoc, schemeModuleTensorMap_comp,
    actualClosedImmersionFactorIdealRestriction_toUnit, Category.comp_id]
  have hs : schemeModuleTensorMap
      ((Scheme.Modules.pullback i).map (closedImmersionModuleToUnit (q ≫ i)) ≫
        pullbackUnitComparison i)
      (𝟙 ((Scheme.Modules.pullback i).obj T)) =
    schemeModuleTensorMap
        ((Scheme.Modules.pullback i).map (closedImmersionModuleToUnit (q ≫ i)))
        (𝟙 ((Scheme.Modules.pullback i).obj T)) ≫
      schemeModuleTensorMap (pullbackUnitComparison i)
        (𝟙 ((Scheme.Modules.pullback i).obj T)) := by
    rw [schemeModuleTensorMap_comp, Category.id_comp]
  rw [hs]
  have hn : (Scheme.Modules.pullback i).map
        (schemeModuleTensorMap (closedImmersionModuleToUnit (q ≫ i)) (𝟙 T)) ≫
      cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap i (schemeModuleUnit Y) T =
    cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap i
        (closedImmersionModule (q ≫ i)) T ≫
      schemeModuleTensorMap
        ((Scheme.Modules.pullback i).map (closedImmersionModuleToUnit (q ≫ i)))
        (𝟙 ((Scheme.Modules.pullback i).obj T)) := by
    exact (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap_naturality i
      (closedImmersionModuleToUnit (q ≫ i)) (𝟙 T)).trans
      (congrArg (fun m => cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap i
          (closedImmersionModule (q ≫ i)) T ≫
        schemeModuleTensorMap
          ((Scheme.Modules.pullback i).map (closedImmersionModuleToUnit (q ≫ i))) m)
        ((Scheme.Modules.pullback i).map_id T))
  rw [← Category.assoc, ← hn]
  exact Category.assoc _ _ _

end PfaffianDescent
