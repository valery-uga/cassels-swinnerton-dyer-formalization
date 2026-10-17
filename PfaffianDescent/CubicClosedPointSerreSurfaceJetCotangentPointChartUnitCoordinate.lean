import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointUnitRegularSection

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] isIso_pullbackUnitComparison

/-- Native actual point-unit coordinates for a module trivialized on an
actual open chart. -/
def cubicClosedPointSerreSurfaceJetCotangent_pointChartUnitIso
    {X U Y : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] (j : Y ⟶ U)
    (M : X.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ SheafOfModules.unit U.ringCatSheaf) :
    (Scheme.Modules.pullback (j ≫ f)).obj M ≅ SheafOfModules.unit Y.ringCatSheaf :=
  cubicClosedPointSerreSurfaceJetCotangent_pointChartModuleIso f j M _ e ≪≫
    asIso (pullbackUnitComparison j)

/-- Actual global sections pulled to the actual point are evaluated by the
literal chart coefficient and the actual structure map of that point. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_pointChartUnitIso_sectionCoordinate
    {X U Y : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] (j : Y ⟶ U)
    (M : X.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ SheafOfModules.unit U.ringCatSheaf)
    (s : M.sections) :
    SheafOfModules.sectionsMap
      (cubicClosedPointSerreSurfaceJetCotangent_pointChartUnitIso f j M e).hom
      (pullbackSection (j ≫ f) M (isIso_pullbackUnitComparison _) s) =
    (SheafOfModules.unit Y.ringCatSheaf).unitHomEquiv
      (unitEndomorphismOfRegularFunction (j.appTop
        (unitEndomorphismValue ((Scheme.Modules.restrictUnitIso f).inv ≫
          (Scheme.Modules.restrictFunctor f).map (M.unitHomEquiv.symm s) ≫ e.hom)))) := by
  let O := SheafOfModules.unit U.ringCatSheaf
  let v := M.unitHomEquiv.symm s
  let m := (Scheme.Modules.restrictUnitIso f).inv ≫
    (Scheme.Modules.restrictFunctor f).map v ≫ e.hom
  let a := unitEndomorphismValue m
  have h := cubicClosedPointSerreSurfaceJetCotangent_pointChartModuleIso_sectionHom
    f j M O e v (unitEndomorphismOfRegularFunction a)
    (unitEndomorphismOfRegularFunction_value m).symm
  rw [M.unitHomEquiv.apply_symm_apply] at h
  exact (SheafOfModules.sectionsMap_comp _ _ _).trans
    ((congrArg (SheafOfModules.sectionsMap (pullbackUnitComparison j)) h).trans
      (cubicClosedPointSerreSurfaceJetCotangent_pointUnit_regularSection j a))

end PfaffianDescent
