import PfaffianDescent.SchemeModuleParameterizedSection
import PfaffianDescent.VoisinGenericPullbackCoordinates

/-! Pullback of the actual universal linear combination retains every
regular coefficient function and the canonical composition isomorphism.
These identities hold on whole parameter charts. -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u v
set_option backward.isDefEq.respectTransparency false

theorem serreActualFiniteCombination_sectionsMap
    {X : Scheme.{u}} {M N : X.Modules} {ι : Type v} [Fintype ι]
    (e : M ⟶ N) (a : ι → (schemeModuleUnit X ⟶ schemeModuleUnit X))
    (s : ι → M.sections) :
    SheafOfModules.sectionsMap e (finiteLinearCombinationSections a s) =
      finiteLinearCombinationSections a (fun i => SheafOfModules.sectionsMap e (s i)) := by
  unfold finiteLinearCombinationSections
  rw [sectionsMap_sumSections]
  congr 1
  funext i
  exact sectionsMap_scaleSection e (a i) (s i)

theorem serreActualFiniteCombination_pullback
    {T X : Scheme.{u}} (f : T ⟶ X) {M : X.Modules}
    {ι : Type v} [Fintype ι] (coeff : ι → Γ(X, ⊤)) (s : ι → M.sections) :
    pullbackSection f M (isIso_pullbackUnitComparison f)
        (finiteLinearCombinationSections
          (fun i => unitEndomorphismOfRegularFunction (coeff i)) s) =
      finiteLinearCombinationSections
        (fun i => unitEndomorphismOfRegularFunction (f.appTop (coeff i)))
        (fun i => pullbackSection f M (isIso_pullbackUnitComparison f) (s i)) := by
  unfold finiteLinearCombinationSections
  rw [pullbackSection_sumSections]
  congr 1
  funext i
  rw [pullbackSection_scaleSection,
    pullbackUnitEndomorphismOfRegularFunction_eq_appTop_general]

theorem serreActualParameterizedSection_pullbackComp
    {K : Type u} [Field K] {X U T : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι : Type v} [Fintype ι] (f : U ⟶ X) (g : T ⟶ U)
    (q : T ⟶ X) (h : g ≫ f = q) (coeff : ι → Γ(U, ⊤))
    (s : ι → SchemeModuleGlobalSectionsOver base M) :
    SheafOfModules.sectionsMap
        (((Scheme.Modules.pullbackComp g f).app M ≪≫
          (Scheme.Modules.pullbackCongr h).app M).hom)
        (pullbackSection g ((Scheme.Modules.pullback f).obj M)
          (isIso_pullbackUnitComparison g)
          (parameterizedSchemeModuleSection base M f coeff s)) =
      parameterizedSchemeModuleSection base M q
        (fun i => g.appTop (coeff i)) s := by
  unfold parameterizedSchemeModuleSection
  rw [serreActualFiniteCombination_pullback, serreActualFiniteCombination_sectionsMap]
  congr 1
  funext i
  exact sectionsMap_pullbackComp_pullbackCongr_pullbackSection
    g f q h M (isIso_pullbackUnitComparison g) (isIso_pullbackUnitComparison f)
    (isIso_pullbackUnitComparison (g ≫ f)) (isIso_pullbackUnitComparison q)
    (schemeModuleGlobalSectionsOverEquivSections base M (s i))

end PfaffianDescent
