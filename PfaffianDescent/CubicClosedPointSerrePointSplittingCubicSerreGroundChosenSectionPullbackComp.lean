import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsCoefficient

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- Literal composition of actual globally pulled sections, as unit-module morphisms. -/
theorem pointSplittingCubicSerreGroundChosenSection_pulledSection_comp
    {K F G : Type u} [Field K] [Field F] [Field G]
    {X Y Z : Scheme.{u}} (base : X ⟶ Spec (.of K))
    (baseY : Y ⟶ Spec (.of F)) (baseZ : Z ⟶ Spec (.of G))
    (f : Z ⟶ Y) (g : Y ⟶ X) (q : Z ⟶ X) (h : f ≫ g = q)
    (M : X.Modules) (s : SchemeModuleGlobalSectionsOver base M) :
    serreActualPulledGlobalSection baseY baseZ f ((Scheme.Modules.pullback g).obj M)
      (serreActualPulledGlobalSection base baseY g M s) ≫
      ((Scheme.Modules.pullbackComp f g).app M ≪≫
        (Scheme.Modules.pullbackCongr h).app M).hom =
      serreActualPulledGlobalSection base baseZ q M s := by
  letI := isIso_pullbackUnitComparison f
  rw [serreActualPulledGlobalSection,
    pullbackSection_unitHomEquiv_symm_eq_inv, Equiv.symm_apply_apply]
  exact pointSplittingGroundKernel_pulledGlobalSection_comp base baseY baseZ f g q h M s

end PfaffianDescent
