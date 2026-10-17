import PfaffianDescent.VoisinGenericPullbackCoordinates
import PfaffianDescent.SchemeModuleGlobalSections

/-! # Actual ground-field-linear pullback evaluation of bundle sections -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

/-- Pulling back an actual global section along an actual scheme map is
linear for the ground-field actions defined by the two structure maps. -/
def cubicClosedPointSerreDegreeThreeEvaluationMap
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (j : Z ⟶ X) (E : X.Modules) :
    SchemeModuleGlobalSectionsOver base E →ₗ[K]
      SchemeModuleGlobalSectionsOver (j ≫ base) ((Scheme.Modules.pullback j).obj E) := by
  let P := Scheme.Modules.pullback j
  letI : IsIso (pullbackUnitComparison j) := isIso_pullbackUnitComparison j
  let u := asIso (pullbackUnitComparison j)
  exact
    { toFun := fun s => u.inv ≫ P.map s
      map_add' := by
        intro s t
        change u.inv ≫ P.map (s + t) = u.inv ≫ P.map s + u.inv ≫ P.map t
        rw [P.map_add, Preadditive.comp_add]
      map_smul' := by
        intro c s
        change u.inv ≫ P.map (schemeModuleConstantEndomorphism base c ≫ s) =
          schemeModuleConstantEndomorphism (j ≫ base) c ≫ (u.inv ≫ P.map s)
        rw [P.map_comp]
        have h : u.inv ≫ P.map (schemeModuleConstantEndomorphism base c) ≫ u.hom =
            schemeModuleConstantEndomorphism (j ≫ base) c := by
          have hpb := pullbackUnitEndomorphismOfRegularFunction_eq_appTop_general j
            (isIso_pullbackUnitComparison j) (affineFunctionHom base c)
          have he : pullbackUnitEndomorphism j (isIso_pullbackUnitComparison j)
              (schemeModuleConstantEndomorphism base c) =
                u.inv ≫ P.map (schemeModuleConstantEndomorphism base c) ≫ u.hom := by
            unfold pullbackUnitEndomorphism
            have hi : Classical.choose (isIso_pullbackUnitComparison j).out = u.inv := by
              apply (cancel_mono u.hom).mp
              exact (Classical.choose_spec (isIso_pullbackUnitComparison j).out).2.trans
                u.inv_hom_id.symm
            rw [hi]
            rfl
          change pullbackUnitEndomorphism j (isIso_pullbackUnitComparison j)
            (schemeModuleConstantEndomorphism base c) = _ at hpb
          rw [he] at hpb
          exact hpb.trans (by
            unfold schemeModuleConstantEndomorphism
            congr 1)
        have hc : u.inv ≫ P.map (schemeModuleConstantEndomorphism base c) =
            schemeModuleConstantEndomorphism (j ≫ base) c ≫ u.inv := by
          apply (cancel_mono u.hom).mp
          calc
            _ = schemeModuleConstantEndomorphism (j ≫ base) c := by
              simpa only [Category.assoc] using h
            _ = _ := by
              rw [Category.assoc, u.inv_hom_id]
              exact (Category.comp_id (schemeModuleConstantEndomorphism (j ≫ base) c)).symm
        rw [← Category.assoc, hc, Category.assoc] }

/-- The evaluation map is the actual pullback of the original morphism
from the unit, with the actual canonical unit comparison. -/
theorem cubicClosedPointSerreDegreeThreeEvaluationMap_apply
    {K : Type u} [Field K] {X Z : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (j : Z ⟶ X) (E : X.Modules)
    (s : SchemeModuleGlobalSectionsOver base E) :
    cubicClosedPointSerreDegreeThreeEvaluationMap base j E s =
      letI : IsIso (pullbackUnitComparison j) := isIso_pullbackUnitComparison j
      inv (pullbackUnitComparison j) ≫ (Scheme.Modules.pullback j).map s := rfl

end PfaffianDescent
