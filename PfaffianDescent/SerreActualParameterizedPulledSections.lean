import PfaffianDescent.SerreActualParameterizedSectionPullback
import PfaffianDescent.SerreActualPointPulledSections

/-! An actual pulled family of global sections, with arbitrary varying
regular coefficients, is the original family along the composite map. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u v
set_option backward.isDefEq.respectTransparency false

theorem serreActualPulledGlobalSection_toSections
    {K L : Type u} [Field K] [Field L] {X Y : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (base' : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (M : X.Modules) (s : SchemeModuleGlobalSectionsOver base M) :
    schemeModuleGlobalSectionsOverEquivSections base' ((Scheme.Modules.pullback f).obj M)
        (serreActualPulledGlobalSection base base' f M s) =
      pullbackSection f M (isIso_pullbackUnitComparison f)
        (schemeModuleGlobalSectionsOverEquivSections base M s) := by
  let N : SheafOfModules.{u} Y.ringCatSheaf := (Scheme.Modules.pullback f).obj M
  exact N.unitHomEquiv.apply_symm_apply _

theorem serreActualParameterizedPulledSections_comp
    {K L : Type u} [Field K] [Field L] {X Y T : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (base' : Y ⟶ Spec (.of L))
    (f : Y ⟶ X) (M : X.Modules)
    {ι : Type v} [Fintype ι] (r : T ⟶ Y) (q : T ⟶ X)
    (h : r ≫ f = q) (coeff : ι → Γ(T, ⊤))
    (s : ι → SchemeModuleGlobalSectionsOver base M) :
    SheafOfModules.sectionsMap
        (((Scheme.Modules.pullbackComp r f).app M ≪≫
          (Scheme.Modules.pullbackCongr h).app M).hom)
        (parameterizedSchemeModuleSection base' ((Scheme.Modules.pullback f).obj M)
          r coeff (fun i => serreActualPulledGlobalSection base base' f M (s i))) =
      parameterizedSchemeModuleSection base M q coeff s := by
  unfold parameterizedSchemeModuleSection
  rw [serreActualFiniteCombination_sectionsMap]
  congr 1
  funext i
  rw [serreActualPulledGlobalSection_toSections]
  exact sectionsMap_pullbackComp_pullbackCongr_pullbackSection r f q h M
    (isIso_pullbackUnitComparison r) (isIso_pullbackUnitComparison f)
    (isIso_pullbackUnitComparison (r ≫ f)) (isIso_pullbackUnitComparison q)
    (schemeModuleGlobalSectionsOverEquivSections base M (s i))

end PfaffianDescent
