import PfaffianDescent.SchemeModuleBaseLinearCategory
import PfaffianDescent.SchemeModuleGlobalSectionsTop

/-! Actual unit Hom and actual global sections with independently defined
pi-induced actions. Both actions already exist; neither is transported
through the comparison to force linearity.
STATUS: SOURCE ONLY / UNVERIFIED. Root owns compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The actual pointwise scalar on a unit Hom equals the independently
constructed original global-section action by constant precomposition.
Equality is proved using actual evaluation on the top open. -/
theorem schemeModuleHomBaseSmul_unit_eq_constant_comp
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) (c : K)
    (f : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M) :
    schemeModuleHomBaseSmul pi c f = schemeModuleConstantEndomorphism pi c ≫ f := by
  let E := schemeModuleGlobalSectionsLinearEquivOpenTop pi M
  let f' : SchemeModuleGlobalSectionsOver pi M := f
  change schemeModuleHomBaseSmul pi c f' =
    (c • f' : SchemeModuleGlobalSectionsOver pi M)
  apply E.injective
  calc
    E (schemeModuleHomBaseSmul pi c f') = c • E f' := by rfl
    _ = E (c • f') := (E.map_smul c f').symm

/-- Identity on the literal underlying morphism, now a K-linear equivalence
between the actual Hom-category action and the original global-section action.
Its scalar compatibility is proved; no action or comparison is supplied. -/
def schemeModuleUnitHomGroundLinearEquivGlobalSections
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M) ≃ₗ[K]
      SchemeModuleGlobalSectionsOver pi M := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  refine
    { toFun := fun f ↦ f
      invFun := fun s ↦ s
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := ?_ }
  intro c f
  change schemeModuleHomBaseSmul pi c f = schemeModuleConstantEndomorphism pi c ≫ f
  exact schemeModuleHomBaseSmul_unit_eq_constant_comp pi M c f

/-- Actual Hom(O_X,M) identifies linearly with the literal Γ(M,top), with
the independently existing original pi-induced scalar on each side. -/
def schemeModuleUnitHomGroundLinearEquivOpenTop
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ((show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M) ≃ₗ[K]
      SchemeModuleOpenSectionsOver pi M ⊤ := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact (schemeModuleUnitHomGroundLinearEquivGlobalSections pi M).trans
    (schemeModuleGlobalSectionsLinearEquivOpenTop pi M)

/-- The actual comparison evaluates the actual morphism at the original
unit section 1. This is the SAME section map used by the original model. -/
theorem schemeModuleUnitHomGroundLinearEquivOpenTop_apply
    (pi : X ⟶ Spec (CommRingCat.of K)) (M : X.Modules) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    ∀ f : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M,
      schemeModuleUnitHomGroundLinearEquivOpenTop pi M f =
        f.val.app (op ⊤) (1 : Γ(X, ⊤)) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  exact fun _ ↦ rfl

/-- Actual coefficient maps commute with the literal comparison, including
the canonical normalization quotient projection. No naturality premise. -/
theorem schemeModuleUnitHomGroundLinearEquivOpenTop_naturality
    (pi : X ⟶ Spec (CommRingCat.of K)) {M N : X.Modules} (g : M ⟶ N)
    (f : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ M) :
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    schemeModuleUnitHomGroundLinearEquivOpenTop pi N (f ≫ g) =
      g.val.app (op ⊤) (schemeModuleUnitHomGroundLinearEquivOpenTop pi M f) := by
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  rfl

end PfaffianDescent.Coray
