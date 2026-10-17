import PfaffianDescent.CechExtDegreeThree

/-!
# Coefficient naturality of degree-three resolution classes

Postcomposing cocycles commutes with the three-step connecting class and the
augmented-chain Ext comparison. This allows coefficient multiplication to
be followed through the Koszul and Cech computations.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A]

namespace DegreeThreeCocycle
/-- Apply a coefficient morphism to every cocycle. -/
def postcompAddHom {C₃ C₄ Y Z : A} (d₄ : C₄ ⟶ C₃) (h : Y ⟶ Z) :
    DegreeThreeCocycle d₄ (Y := Y) →+ DegreeThreeCocycle d₄ (Y := Z) where
  toFun f := ⟨f.1 ≫ h, by
    change d₄ ≫ (f.1 ≫ h) = 0
    rw [← Category.assoc, show d₄ ≫ f.1 = 0 from f.2, zero_comp]⟩
  map_zero' := by apply Subtype.ext; exact zero_comp
  map_add' f g := by
    apply Subtype.ext
    change (f.1 + g.1) ≫ h = f.1 ≫ h + g.1 ≫ h
    simp only [Preadditive.add_comp]

@[simp]
theorem postcompAddHom_apply_val {C₃ C₄ Y Z : A}
    (d₄ : C₄ ⟶ C₃) (h : Y ⟶ Z) (f : DegreeThreeCocycle d₄ (Y := Y)) :
    (postcompAddHom d₄ h f).1 = f.1 ≫ h := rfl
end DegreeThreeCocycle

variable [HasExt.{w} A]

/-- Coefficient postcomposition commutes with the three connecting maps. -/
theorem ThreeStepResolution.connecting_postcomp
    (R : ThreeStepResolution A) {Y Z : A} (x : R.K₂ ⟶ Y) (h : Y ⟶ Z) :
    (R.connecting Y x).comp (Ext.mk₀ h) (add_zero 3) = R.connecting Z (x ≫ h) := by
  simp only [ThreeStepResolution.connecting, Ext.comp_assoc, Ext.mk₀_comp_mk₀]

/-- The cocycle descent respects coefficient morphisms. -/
theorem degreeThreeCocycleDesc_postcomp
    {C₂ C₃ C₄ Y Z : A} (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₄₃ : d₄ ≫ d₃ = 0) (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact)
    (f : DegreeThreeCocycle d₄ (Y := Y)) (h : Y ⟶ Z) :
    degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃
      (DegreeThreeCocycle.postcompAddHom d₄ h f) =
        degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ f ≫ h := by
  apply (cancel_epi (Abelian.coimage.π d₃)).1
  rw [coimage_π_comp_degreeThreeCocycleDesc, ← Category.assoc,
    coimage_π_comp_degreeThreeCocycleDesc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The augmented resolution comparison respects coefficient morphisms. -/
theorem augmentedChainDegreeThreeToExt_postcomp
    (P C₀ C₁ C₂ C₃ C₄ Y Z : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0) (h₄₃ : d₄ ≫ d₃ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact)
    [Epi epsilon] (f : DegreeThreeCocycle d₄ (Y := Y)) (h : Y ⟶ Z) :
    (augmentedChainDegreeThreeToExt P C₀ C₁ C₂ C₃ C₄ Y epsilon d₁ d₂ d₃ d₄
      h₁₀ h₂₁ h₃₂ h₄₃ hexact₀ hexact₁ hexact₂ hexact₃ f).comp (Ext.mk₀ h) (add_zero 3) =
    augmentedChainDegreeThreeToExt P C₀ C₁ C₂ C₃ C₄ Z epsilon d₁ d₂ d₃ d₄
      h₁₀ h₂₁ h₃₂ h₄₃ hexact₀ hexact₁ hexact₂ hexact₃
        (DegreeThreeCocycle.postcompAddHom d₄ h f) := by
  unfold augmentedChainDegreeThreeToExt
  rw [ThreeStepResolution.connecting_postcomp, degreeThreeCocycleDesc_postcomp]
end PfaffianDescent
