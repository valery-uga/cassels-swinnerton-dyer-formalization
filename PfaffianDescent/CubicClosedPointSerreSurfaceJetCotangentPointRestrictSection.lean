import PfaffianDescent.BundleSectionZeroLocusNaturality

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual point pullback agrees with point pullback of an actual open restriction. -/
def cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso
    {X U Y : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (j : Y ⟶ U) (M : X.Modules) :
    (Scheme.Modules.pullback (j ≫ f)).obj M ≅
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.restrictFunctor f).obj M) :=
  ((Scheme.Modules.pullbackComp j f).app M).symm ≪≫
    (Scheme.Modules.pullback j).mapIso ((Scheme.Modules.restrictFunctorIsoPullback f).app M).symm

/-- This native fibre comparison carries the actual pulled global section
to the actual point pullback of its literal chart restriction. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso_section
    {X U Y : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f]
    (j : Y ⟶ U) (M : X.Modules) (s : M.sections) :
    SheafOfModules.sectionsMap
      (cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso f j M).hom
      (pullbackSection (j ≫ f) M (isIso_pullbackUnitComparison _) s) =
    pullbackSection j ((Scheme.Modules.restrictFunctor f).obj M)
      (isIso_pullbackUnitComparison _) (restrictModuleSection f M s) := by
  let A := (Scheme.Modules.restrictFunctorIsoPullback f).app M
  let B := (Scheme.Modules.pullbackComp j f).app M
  let r := restrictModuleSection f M s
  let sf := pullbackSection f M (isIso_pullbackUnitComparison _) s
  have hR : SheafOfModules.sectionsMap A.inv sf = r :=
    (congrArg (SheafOfModules.sectionsMap A.inv)
      (restrictModuleSection_to_pullbackSection f (isIso_pullbackUnitComparison _) s)).symm.trans
      (sectionsMap_hom_inv A.symm r)
  have hC := pullbackSection_comp j f M (isIso_pullbackUnitComparison _)
    (isIso_pullbackUnitComparison _) (isIso_pullbackUnitComparison _) s
  calc
    _ = SheafOfModules.sectionsMap ((Scheme.Modules.pullback j).map A.inv)
        (SheafOfModules.sectionsMap B.inv
          (pullbackSection (j ≫ f) M (isIso_pullbackUnitComparison _) s)) :=
      SheafOfModules.sectionsMap_comp _ _ _
    _ = SheafOfModules.sectionsMap ((Scheme.Modules.pullback j).map A.inv)
        (pullbackSection j ((Scheme.Modules.pullback f).obj M)
          (isIso_pullbackUnitComparison _) sf) :=
      congrArg (SheafOfModules.sectionsMap ((Scheme.Modules.pullback j).map A.inv)) hC
    _ = pullbackSection j ((Scheme.Modules.restrictFunctor f).obj M)
        (isIso_pullbackUnitComparison _) (SheafOfModules.sectionsMap A.inv sf) :=
      sectionsMap_pullbackSection j A.inv (isIso_pullbackUnitComparison _) sf
    _ = _ := congrArg (pullbackSection j ((Scheme.Modules.restrictFunctor f).obj M)
      (isIso_pullbackUnitComparison _)) hR

end PfaffianDescent
