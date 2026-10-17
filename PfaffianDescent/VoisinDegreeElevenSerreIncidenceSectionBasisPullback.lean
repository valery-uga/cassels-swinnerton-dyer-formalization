import PfaffianDescent.VoisinGenericPullbackCoordinates
import PfaffianDescent.SchemeModuleParameterizedSection

/-! # Canonical basis combinations recover actual sections after pullback -/
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceBasisSection_reconstruct
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (s : SchemeModuleGlobalSectionsOver base M) :
    finiteLinearCombinationSections
      (fun i => schemeModuleConstantEndomorphism base
        ((Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s i))
      (fun i => schemeModuleGlobalSectionsOverEquivSections base M
        (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i)) =
      schemeModuleGlobalSectionsOverEquivSections base M s := by
  apply M.unitHomEquiv.symm.injective
  unfold finiteLinearCombinationSections
  rw [sumSections_unitHomEquiv_symm]
  simp only [scaleSection, schemeModuleGlobalSectionsOverEquivSections,
    Equiv.symm_apply_apply]
  have hs := M.unitHomEquiv.symm_apply_apply s
  have hb : ∀ i, M.unitHomEquiv.symm
      (M.unitHomEquiv (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i)) =
      Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i :=
    fun i => M.unitHomEquiv.symm_apply_apply _
  have hr : (∑ i, schemeModuleConstantEndomorphism base
      ((Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s i) ≫
      Module.finBasis K (SchemeModuleGlobalSectionsOver base M) i) = s :=
    (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).sum_repr s
  exact (Finset.sum_congr rfl (fun i _ => congrArg (fun t =>
    schemeModuleConstantEndomorphism base
      ((Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s i) ≫ t)
        (hb i))).trans (hr.trans hs.symm)

/-- The actual canonical basis coefficients, pulled as regular functions,
produce the actual pulled-back section itself. -/
theorem serreIncidenceParameterizedBasis_eq_pullback
    {K : Type u} [Field K] {X B : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (f : B ⟶ X) (s : SchemeModuleGlobalSectionsOver base M) :
    parameterizedSchemeModuleSection base M f
      (fun i => f.appTop (affineFunctionHom base
        ((Module.finBasis K (SchemeModuleGlobalSectionsOver base M)).repr s i)))
      (Module.finBasis K (SchemeModuleGlobalSectionsOver base M)) =
    pullbackSection f M (isIso_pullbackUnitComparison f)
      (schemeModuleGlobalSectionsOverEquivSections base M s) := by
  rw [← serreIncidenceBasisSection_reconstruct base M s]
  unfold finiteLinearCombinationSections
  rw [pullbackSection_sumSections]
  simp_rw [pullbackSection_scaleSection,
    schemeModuleConstantEndomorphism,
    pullbackUnitEndomorphismOfRegularFunction_eq_appTop_general]
  rfl

end PfaffianDescent
