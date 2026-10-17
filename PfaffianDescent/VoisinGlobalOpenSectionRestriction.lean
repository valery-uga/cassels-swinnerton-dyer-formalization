import PfaffianDescent.VoisinFieldBaseChangeGlobalComparison
import PfaffianDescent.SchemeModuleGlobalSectionsTop
import PfaffianDescent.SchemeModuleCoverEqualizer

/-!
# Restricting a global module section to an affine open

This identifies two canonical presentations of the same local section:
restriction of its value on the top open, and the value of the restricted
categorical section.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus

universe u

noncomputable section

/-- Global-to-top equivalence followed by open restriction agrees with
restricting the categorical global section and reading its top-open value. -/
theorem schemeModuleGlobalSections_openRestriction_eq_sectionValue
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    (U : X.Opens) (σ : M.sections) :
    schemeModuleOpenSectionsRestrictionLinearMap base M
      (show U ≤ ⊤ from le_top)
      (schemeModuleGlobalSectionsLinearEquivOpenTop base M
        ((schemeModuleGlobalSectionsOverEquivSections base M).symm σ)) =
      σ.val (Opposite.op U) := by
  have htop : schemeModuleGlobalSectionsLinearEquivOpenTop base M
      ((schemeModuleGlobalSectionsOverEquivSections base M).symm σ) =
      schemeModuleSectionsEquivTop M σ := by
    change schemeModuleSectionsEquivTop M
      ((schemeModuleGlobalSectionsOverEquivSections base M)
        ((schemeModuleGlobalSectionsOverEquivSections base M).symm σ)) =
      schemeModuleSectionsEquivTop M σ
    rw [(schemeModuleGlobalSectionsOverEquivSections base M).apply_symm_apply]
  rw [htop]
  change (M.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom
    (σ.val (Opposite.op ⊤)) = σ.val (Opposite.op U)
  exact σ.property _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical restricted categorical section has the original
global section's value on the chosen open. -/
theorem moduleRestrictTop_restrictModuleSection_eq_sectionValue
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    (U : X.Opens) (σ : M.sections) :
    moduleRestrictTopLinearEquivOpenSectionsOver base M U
      (schemeModuleSectionsEquivTop (M.restrict U.ι)
        (restrictModuleSection U.ι M σ)) =
      σ.val (Opposite.op U) := by
  change (M.restrictAppIso U.ι ⊤ ≪≫
      M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).hom
      ((restrictModuleSection U.ι M σ).val (Opposite.op ⊤)) =
    σ.val (Opposite.op U)
  unfold restrictModuleSection
  rw [SheafOfModules.unitHomEquiv_apply_coe]
  simp only [Iso.trans_hom, ConcreteCategory.comp_apply]
  erw [ConcreteCategory.comp_apply]
  have hone :
      (((Scheme.Modules.restrictUnitIso U.ι).symm.hom.val.app
        (Opposite.op ⊤)).hom (1 : Γ((U : Scheme.{u}), ⊤))) =
      (1 : Γ(X, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) := by
    change ((U.ι.appIso ⊤).inv.hom 1) = 1
    exact map_one _
  rw [hone]
  have hφ :
      (((Scheme.Modules.restrictFunctor U.ι).map
        (M.unitHomEquiv.symm σ)).val.app (Opposite.op ⊤)).hom
          (1 : Γ(X, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) =
      σ.val (Opposite.op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))) := by
    change (((M.unitHomEquiv.symm σ).val.app
      (Opposite.op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))).hom
      (1 : Γ(X, U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))) = _
    rw [← SheafOfModules.unitHomEquiv_apply_coe]
    exact congrArg
      (fun z => z.val (Opposite.op
        (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens))))
      (M.unitHomEquiv.apply_symm_apply σ)
  rw [hφ]
  change (M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).hom
      (σ.val (Opposite.op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))) =
    σ.val (Opposite.op U)
  change (M.presheaf.map (eqToIso U.ι_image_top.symm).op.hom).hom
      (σ.val (Opposite.op (U.ι ''ᵁ (⊤ : (U : Scheme.{u}).Opens)))) =
    σ.val (Opposite.op U)
  exact σ.property _

/-- Both canonical routes from a categorical global section to an
open section agree: evaluate at the top open and restrict, or restrict the
module section and then read its top-open value. -/
theorem schemeModuleGlobalSections_openRestriction_eq_restrictModuleSection
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    (U : X.Opens) (σ : M.sections) :
    schemeModuleOpenSectionsRestrictionLinearMap base M
      (show U ≤ ⊤ from le_top)
      (schemeModuleGlobalSectionsLinearEquivOpenTop base M
        ((schemeModuleGlobalSectionsOverEquivSections base M).symm σ)) =
      moduleRestrictTopLinearEquivOpenSectionsOver base M U
        (schemeModuleSectionsEquivTop (M.restrict U.ι)
          (restrictModuleSection U.ι M σ)) := by
  exact (schemeModuleGlobalSections_openRestriction_eq_sectionValue
    base M U σ).trans
      (moduleRestrictTop_restrictModuleSection_eq_sectionValue
        base M U σ).symm

/-- Any linear evaluation on an open section takes the same value
whether a global section is first converted to its top-open value and
restricted or directly restricted as a categorical section. -/
theorem globalSectionOpenLinearEvaluation_apply
    {K : Type u} [Field K] {X : Scheme.{u}}
    (base : X ⟶ Spec (.of K)) (M : X.Modules)
    (U : X.Opens)
    (ev : SchemeModuleOpenSectionsOver base M U →ₗ[K] K)
    (σ : M.sections) :
    (ev.comp ((schemeModuleOpenSectionsRestrictionLinearMap base M
      (show U ≤ ⊤ from le_top)).comp
      (schemeModuleGlobalSectionsLinearEquivOpenTop base M).toLinearMap))
      ((schemeModuleGlobalSectionsOverEquivSections base M).symm σ) =
    ev (moduleRestrictTopLinearEquivOpenSectionsOver base M U
      (schemeModuleSectionsEquivTop (M.restrict U.ι)
        (restrictModuleSection U.ι M σ))) := by
  simp only [LinearMap.comp_apply]
  exact congrArg ev
    (schemeModuleGlobalSections_openRestriction_eq_restrictModuleSection
      base M U σ)

end

end PfaffianDescent
