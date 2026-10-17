import PfaffianDescent.SchemeModuleParameterizedSection

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u v
set_option backward.isDefEq.respectTransparency false

/-- A genuine section combination is invariant under a simultaneous finite reindex. -/
theorem pointSplittingCubicSerreGroundChosenSection_finiteCombination_reindex
    {X : Scheme.{u}} {M : X.Modules} {ι κ : Type v} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (a : ι → (schemeModuleUnit X ⟶ schemeModuleUnit X))
    (s : ι → M.sections) :
    finiteLinearCombinationSections a s =
      finiteLinearCombinationSections (fun j => a (e.symm j)) (fun j => s (e.symm j)) := by
  apply M.unitHomEquiv.symm.injective
  simp only [finiteLinearCombinationSections, sumSections_unitHomEquiv_symm]
  exact (e.symm.sum_comp (fun i => M.unitHomEquiv.symm (scaleSection (a i) (s i)))).symm

/-- The actual parameterized pullback section is unchanged by simultaneous coefficient/section reindex. -/
theorem pointSplittingCubicSerreGroundChosenSection_parameterizedSection_reindex
    {K : Type u} [Field K] {X U : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    {ι κ : Type v} [Fintype ι] [Fintype κ] (e : ι ≃ κ)
    (f : U ⟶ X) (coeff : ι → Γ(U, ⊤))
    (s : ι → SchemeModuleGlobalSectionsOver base M) :
    parameterizedSchemeModuleSection (K := K) base M f coeff s =
      parameterizedSchemeModuleSection (K := K) base M f
        (fun j => coeff (e.symm j)) (fun j => s (e.symm j)) := by
  unfold parameterizedSchemeModuleSection
  exact pointSplittingCubicSerreGroundChosenSection_finiteCombination_reindex e _ _

end PfaffianDescent
