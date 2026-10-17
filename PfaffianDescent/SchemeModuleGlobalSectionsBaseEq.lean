import PfaffianDescent.SchemeModuleGlobalSections

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Equal ground structure maps give the identity equivalence on the actual
morphism-valued global sections. Only the scalar action needs transport. -/
def schemeModuleGlobalSectionsBaseEqLinearEquiv
    {K : Type u} [Field K] {X : Scheme.{u}}
    (b b' : X ⟶ Spec (.of K)) (h : b = b') (M : X.Modules) :
    SchemeModuleGlobalSectionsOver b M ≃ₗ[K]
      SchemeModuleGlobalSectionsOver b' M where
  toFun s := s
  invFun s := s
  left_inv s := rfl
  right_inv s := rfl
  map_add' s t := rfl
  map_smul' c s := by
    cases h
    rfl

@[simp] lemma schemeModuleGlobalSectionsBaseEqLinearEquiv_apply
    {K : Type u} [Field K] {X : Scheme.{u}}
    (b b' : X ⟶ Spec (.of K)) (h : b = b') (M : X.Modules)
    (s : SchemeModuleGlobalSectionsOver b M) :
    schemeModuleGlobalSectionsBaseEqLinearEquiv b b' h M s = s := rfl

end PfaffianDescent
