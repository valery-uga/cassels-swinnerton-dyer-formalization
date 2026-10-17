import PfaffianDescent.SchemeModuleCoverEqualizer
import PfaffianDescent.SchemeModuleGlobalSections

/-!
# Morphism-valued global sections and sections on the top open

The project uses morphisms from the unit module as its finite-dimensional
global-section model.  The Cech argument uses evaluation on the top open.
This file identifies the two models, including their ground-field linear
structures.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory Opposite BundleSectionZeroLocus

universe u

noncomputable section

/-- A compatible family of sections is determined by its value on the top
open; conversely, a top-open section restricts to such a family. -/
noncomputable def schemeModuleSectionsEquivTop
    {X : Scheme.{u}} (M : X.Modules) : M.sections ≃ Γ(M, ⊤) where
  toFun s := s.1 (op ⊤)
  invFun t := PresheafOfModules.sectionsMk
    (fun U ↦ M.presheaf.map
      (homOfLE (show U.unop ≤ ⊤ from le_top)).op t)
    (by
      intro U V f
      have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
      rw [hf]
      exact (PresheafOfModules.map_comp_apply M.val
        (homOfLE (show U.unop ≤ ⊤ from le_top)).op
        (homOfLE (leOfHom f.unop)).op t).symm)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  right_inv t := by
    change M.presheaf.map (homOfLE (show ⊤ ≤ ⊤ from le_rfl)).op t = t
    simpa using congr_fun (M.presheaf.map_id (op ⊤)) t

/-- The morphism-valued and top-open models of global module sections are
additively equivalent. -/
noncomputable def schemeModuleGlobalSectionsAddEquivOpenTop
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (M : X.Modules) :
    SchemeModuleGlobalSectionsOver p M ≃+
      SchemeModuleOpenSectionsOver p M ⊤ where
  toFun s := (schemeModuleGlobalSectionsOverEquivSections p M s).1 (op ⊤)
  invFun t := (schemeModuleGlobalSectionsOverEquivSections p M).symm
    ((schemeModuleSectionsEquivTop M).symm t)
  left_inv s := by
    apply (schemeModuleGlobalSectionsOverEquivSections p M).injective
    change (schemeModuleGlobalSectionsOverEquivSections p M)
        ((schemeModuleGlobalSectionsOverEquivSections p M).symm
          ((schemeModuleSectionsEquivTop M).symm
            (schemeModuleSectionsEquivTop M
              (schemeModuleGlobalSectionsOverEquivSections p M s)))) =
      schemeModuleGlobalSectionsOverEquivSections p M s
    rw [(schemeModuleGlobalSectionsOverEquivSections p M).apply_symm_apply,
      (schemeModuleSectionsEquivTop M).symm_apply_apply]
  right_inv t := by
    change schemeModuleSectionsEquivTop M
        ((schemeModuleGlobalSectionsOverEquivSections p M)
          ((schemeModuleGlobalSectionsOverEquivSections p M).symm
            ((schemeModuleSectionsEquivTop M).symm t))) = t
    rw [(schemeModuleGlobalSectionsOverEquivSections p M).apply_symm_apply]
    change schemeModuleSectionsEquivTop M
        ((schemeModuleSectionsEquivTop M).symm (show Γ(M, ⊤) from t)) =
      (show Γ(M, ⊤) from t)
    exact (schemeModuleSectionsEquivTop M).apply_symm_apply t
  map_add' s t := by
    change ((s + t).val.app (op ⊤)).hom (1 : Γ(X, ⊤)) =
      (s.val.app (op ⊤)).hom (1 : Γ(X, ⊤)) +
        (t.val.app (op ⊤)).hom (1 : Γ(X, ⊤))
    rfl

/-- The two global-section models are linearly equivalent over the ground
field. -/
noncomputable def schemeModuleGlobalSectionsLinearEquivOpenTop
    {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) (M : X.Modules) :
    SchemeModuleGlobalSectionsOver p M ≃ₗ[K]
      SchemeModuleOpenSectionsOver p M ⊤ where
  __ := schemeModuleGlobalSectionsAddEquivOpenTop p M
  map_smul' c s := by
    let r : Γ(X, ⊤) := affineFunctionHom p c
    have ha :
        (schemeModuleConstantEndomorphism p c).app ⊤
            (1 : Γ(X, ⊤)) = r := by
      exact unitEndomorphismValue_ofRegularFunction (X := X) r
    have hs := Scheme.Modules.Hom.app_smul s r (1 : Γ(X, ⊤))
    change s.app ⊤
        ((schemeModuleConstantEndomorphism p c).app ⊤
          (1 : Γ(X, ⊤))) =
      schemeOpenBaseRingHom p ⊤ c •
        s.app ⊤ (1 : Γ(X, ⊤))
    rw [ha, schemeOpenBaseRingHom_top_apply]
    have hrone : r • (1 : Γ(X, ⊤)) = r := by
      change r * 1 = r
      exact mul_one r
    calc
      s.app ⊤ r = s.app ⊤ (r • (1 : Γ(X, ⊤))) :=
        congrArg (fun q : Γ(X, ⊤) ↦ s.app ⊤ q) hrone.symm
      _ = r • s.app ⊤ (1 : Γ(X, ⊤)) := hs
      _ = affineFunctionHom p c • s.app ⊤ (1 : Γ(X, ⊤)) := rfl

end

end PfaffianDescent
