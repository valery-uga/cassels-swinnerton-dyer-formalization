import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointChartSectionHom
import PfaffianDescent.CubicPointTraceFieldBaseChangeConstantPullback

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] isIso_pullbackUnitComparison

/-- The canonical unit comparison evaluates actual pulled regular sections
by the literal structure-sheaf map, for an arbitrary scheme morphism. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_pointUnit_regularSection
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Γ(Y, ⊤)) :
    SheafOfModules.sectionsMap (pullbackUnitComparison f)
      (pullbackSection f (SheafOfModules.unit Y.ringCatSheaf)
        (isIso_pullbackUnitComparison _) ((SheafOfModules.unit Y.ringCatSheaf).unitHomEquiv
          (unitEndomorphismOfRegularFunction a))) =
      (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv
        (unitEndomorphismOfRegularFunction (f.appTop a)) := by
  let O := SheafOfModules.unit X.ringCatSheaf
  let c := pullbackUnitComparison f
  apply O.unitHomEquiv.symm.injective
  rw [← SheafOfModules.unitHomEquiv_symm_comp,
    pullbackSection_unitHomEquiv_symm_eq_inv, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rw [Category.assoc, cubicPointTraceFieldBaseChange_pullbackUnit_regularFunction]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

end PfaffianDescent
