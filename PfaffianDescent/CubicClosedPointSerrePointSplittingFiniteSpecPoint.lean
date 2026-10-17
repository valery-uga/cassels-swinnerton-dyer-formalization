import PfaffianDescent.BundleSectionZeroLocusNaturality
import PfaffianDescent.CubicClosedPointSerrePointSplittingFiniteSpecSections

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

def pointSplittingFiniteSpecPointModuleIso
    {D T : Scheme.{u}} [IsAffine D]
    (j : T ⟶ Spec (.of Γ(D, ⊤))) (δ : T ⟶ D)
    (h : j = δ ≫ D.isoSpec.hom) (N : D.Modules) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback D.isoSpec.inv).obj N) ≅
      (Scheme.Modules.pullback δ).obj N :=
  (Scheme.Modules.pullbackComp j D.isoSpec.inv).app N ≪≫
    (Scheme.Modules.pullbackCongr (show j ≫ D.isoSpec.inv = δ by
      rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id])).app N

/-- The point-fiber comparison preserves the literal pullback of the SAME
finite-scheme section through its canonical spectrum presentation. -/
theorem pointSplittingFiniteSpecPointModuleIso_section
    {D T : Scheme.{u}} [IsAffine D]
    (j : T ⟶ Spec (.of Γ(D, ⊤))) (δ : T ⟶ D)
    (h : j = δ ≫ D.isoSpec.hom) (N : D.Modules) (s : N.sections) :
    SheafOfModules.sectionsMap (pointSplittingFiniteSpecPointModuleIso j δ h N).hom
      (pullbackSection j ((Scheme.Modules.pullback D.isoSpec.inv).obj N)
        (isIso_pullbackUnitComparison _)
        (pullbackSection D.isoSpec.inv N (isIso_pullbackUnitComparison _) s)) =
    pullbackSection δ N (isIso_pullbackUnitComparison _) s := by
  exact sectionsMap_pullbackComp_pullbackCongr_pullbackSection j D.isoSpec.inv δ
    (show j ≫ D.isoSpec.inv = δ by
      rw [h, Category.assoc, Iso.hom_inv_id, Category.comp_id]) N
    (isIso_pullbackUnitComparison _) (isIso_pullbackUnitComparison _)
    (isIso_pullbackUnitComparison _) (isIso_pullbackUnitComparison _) s

end PfaffianDescent
