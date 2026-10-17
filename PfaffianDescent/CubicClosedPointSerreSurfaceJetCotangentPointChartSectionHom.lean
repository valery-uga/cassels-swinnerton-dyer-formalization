import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointRestrictSection

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual point-fibre coordinates through an actual chart module isomorphism. -/
def cubicClosedPointSerreSurfaceJetCotangent_pointChartModuleIso
    {X U Y : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] (j : Y ⟶ U)
    (M : X.Modules) (N : U.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N) :
    (Scheme.Modules.pullback (j ≫ f)).obj M ≅ (Scheme.Modules.pullback j).obj N :=
  cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso f j M ≪≫
    (Scheme.Modules.pullback j).mapIso e

/-- A literal chart-section morphism square yields the actual global-section
to actual point-fibre square, with native pullback unit coordinates. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_pointChartModuleIso_sectionHom
    {X U Y : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] (j : Y ⟶ U)
    (M : X.Modules) (N : U.Modules)
    (e : (Scheme.Modules.restrictFunctor f).obj M ≅ N)
    (v : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (t : SheafOfModules.unit U.ringCatSheaf ⟶ N)
    (h : (Scheme.Modules.restrictUnitIso f).inv ≫
      (Scheme.Modules.restrictFunctor f).map v ≫ e.hom = t) :
    SheafOfModules.sectionsMap
      (cubicClosedPointSerreSurfaceJetCotangent_pointChartModuleIso f j M N e).hom
      (pullbackSection (j ≫ f) M (isIso_pullbackUnitComparison _) (M.unitHomEquiv v)) =
    pullbackSection j N (isIso_pullbackUnitComparison _) (N.unitHomEquiv t) := by
  let r := restrictModuleSection f M (M.unitHomEquiv v)
  have hr : SheafOfModules.sectionsMap e.hom r = N.unitHomEquiv t := by
    apply N.unitHomEquiv.symm.injective
    rw [← SheafOfModules.unitHomEquiv_symm_comp r e.hom]
    unfold r restrictModuleSection
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact h
  calc
    _ = SheafOfModules.sectionsMap ((Scheme.Modules.pullback j).map e.hom)
        (SheafOfModules.sectionsMap
          (cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso f j M).hom
          (pullbackSection (j ≫ f) M (isIso_pullbackUnitComparison _) (M.unitHomEquiv v))) :=
      SheafOfModules.sectionsMap_comp _ _ _
    _ = SheafOfModules.sectionsMap ((Scheme.Modules.pullback j).map e.hom)
        (pullbackSection j ((Scheme.Modules.restrictFunctor f).obj M)
          (isIso_pullbackUnitComparison _) r) :=
      congrArg (SheafOfModules.sectionsMap ((Scheme.Modules.pullback j).map e.hom))
        (cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso_section f j M _)
    _ = pullbackSection j N (isIso_pullbackUnitComparison _)
        (SheafOfModules.sectionsMap e.hom r) :=
      sectionsMap_pullbackSection j e.hom (isIso_pullbackUnitComparison _) r
    _ = _ := congrArg (pullbackSection j N (isIso_pullbackUnitComparison _)) hr

end PfaffianDescent
