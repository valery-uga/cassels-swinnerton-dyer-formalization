import PfaffianDescent.CechExtDegreeTwo

/-!
# Coefficient naturality of degree-two resolution classes

Postcomposing cocycles commutes with the two-step connecting class and the
augmented-chain Ext comparison. This allows coefficient multiplication to
be followed through the Koszul and Cech computations.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A]

namespace DegreeTwoCocycle
/-- Apply a coefficient morphism to every cocycle. -/
def postcompAddHom {C₂ C₃ Y Z : A} (d₃ : C₃ ⟶ C₂) (h : Y ⟶ Z) :
    DegreeTwoCocycle d₃ (Y := Y) →+ DegreeTwoCocycle d₃ (Y := Z) where
  toFun f := ⟨f.1 ≫ h, by
    change d₃ ≫ (f.1 ≫ h) = 0
    rw [← Category.assoc, show d₃ ≫ f.1 = 0 from f.2, zero_comp]⟩
  map_zero' := by apply Subtype.ext; exact zero_comp
  map_add' f g := by
    apply Subtype.ext
    change (f.1 + g.1) ≫ h = f.1 ≫ h + g.1 ≫ h
    simp only [Preadditive.add_comp]

@[simp]
theorem postcompAddHom_apply_val {C₂ C₃ Y Z : A}
    (d₃ : C₃ ⟶ C₂) (h : Y ⟶ Z) (f : DegreeTwoCocycle d₃ (Y := Y)) :
    (postcompAddHom d₃ h f).1 = f.1 ≫ h := rfl
end DegreeTwoCocycle

variable [HasExt.{w} A]

/-- Coefficient postcomposition commutes with the two connecting maps. -/
theorem TwoStepResolution.connecting_postcomp
    (R : TwoStepResolution A) {Y Z : A} (x : R.K₁ ⟶ Y) (h : Y ⟶ Z) :
    (R.connecting Y x).comp (Ext.mk₀ h) (add_zero 2) = R.connecting Z (x ≫ h) := by
  simp only [TwoStepResolution.connecting, Ext.comp_assoc, Ext.mk₀_comp_mk₀]

/-- The cocycle descent respects coefficient morphisms. -/
theorem degreeTwoCocycleDesc_postcomp
    {C₁ C₂ C₃ Y Z : A} (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂)
    (h₃₂ : d₃ ≫ d₂ = 0) (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (f : DegreeTwoCocycle d₃ (Y := Y)) (h : Y ⟶ Z) :
    degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂
      (DegreeTwoCocycle.postcompAddHom d₃ h f) =
        degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f ≫ h := by
  apply (cancel_epi (Abelian.coimage.π d₂)).1
  rw [coimage_π_comp_degreeTwoCocycleDesc, ← Category.assoc,
    coimage_π_comp_degreeTwoCocycleDesc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The augmented resolution comparison respects coefficient morphisms. -/
theorem augmentedChainDegreeTwoToExt_postcomp
    (P C₀ C₁ C₂ C₃ Y Z : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0) (h₃₂ : d₃ ≫ d₂ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    [Epi epsilon] (f : DegreeTwoCocycle d₃ (Y := Y)) (h : Y ⟶ Z) :
    (augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y epsilon d₁ d₂ d₃
      h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ f).comp (Ext.mk₀ h) (add_zero 2) =
    augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Z epsilon d₁ d₂ d₃
      h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ (DegreeTwoCocycle.postcompAddHom d₃ h f) := by
  unfold augmentedChainDegreeTwoToExt
  rw [TwoStepResolution.connecting_postcomp, degreeTwoCocycleDesc_postcomp]
end PfaffianDescent
