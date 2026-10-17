import PfaffianDescent.TwoStepResolutionComparison

/-!
# Source naturality of the augmented degree-two Ext comparison

An explicit chain comparison carries coefficient cocycles to the class
pulled back along the augmentation-target map. No kernel-object comparison
data is assumed; the needed maps are obtained from exactness.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A]

namespace DegreeTwoCocycle
/-- Precompose cocycles along a commuting pair of source differentials. -/
def precompAddHom {C₂ C₃ D₂ D₃ Y : A}
    (d₃ : C₃ ⟶ C₂) (e₃ : D₃ ⟶ D₂)
    (a₂ : C₂ ⟶ D₂) (a₃ : C₃ ⟶ D₃)
    (h : d₃ ≫ a₂ = a₃ ≫ e₃) :
    DegreeTwoCocycle e₃ (Y := Y) →+ DegreeTwoCocycle d₃ (Y := Y) where
  toFun f := ⟨a₂ ≫ f.1, by
    change d₃ ≫ (a₂ ≫ f.1) = 0
    rw [← Category.assoc, h, Category.assoc,
      show e₃ ≫ f.1 = 0 from f.2, comp_zero]⟩
  map_zero' := by apply Subtype.ext; exact comp_zero
  map_add' f g := by
    apply Subtype.ext
    change a₂ ≫ (f.1 + g.1) = a₂ ≫ f.1 + a₂ ≫ g.1
    simp only [Preadditive.comp_add]
end DegreeTwoCocycle

variable [HasExt.{w} A]
set_option backward.isDefEq.respectTransparency false in
/-- A comparison of augmented chains yields the actual source pullback
formula for degree-two Ext classes, directly on their coefficient cocycles. -/
theorem augmentedChainDegreeTwoToExt_precomp
    (P C₀ C₁ C₂ C₃ Q D₀ D₁ D₂ D₃ Y : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁) (d₃ : C₃ ⟶ C₂)
    (eta : D₀ ⟶ Q) (e₁ : D₁ ⟶ D₀) (e₂ : D₂ ⟶ D₁) (e₃ : D₃ ⟶ D₂)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0) (h₃₂ : d₃ ≫ d₂ = 0)
    (k₁₀ : e₁ ≫ eta = 0) (k₂₁ : e₂ ≫ e₁ = 0) (k₃₂ : e₃ ≫ e₂ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (kexact₀ : (ShortComplex.mk e₁ eta k₁₀).Exact)
    (kexact₁ : (ShortComplex.mk e₂ e₁ k₂₁).Exact)
    (kexact₂ : (ShortComplex.mk e₃ e₂ k₃₂).Exact)
    [Epi epsilon] [Epi eta]
    (g : P ⟶ Q) (a₀ : C₀ ⟶ D₀) (a₁ : C₁ ⟶ D₁)
    (a₂ : C₂ ⟶ D₂) (a₃ : C₃ ⟶ D₃)
    (haug : epsilon ≫ g = a₀ ≫ eta)
    (hfirst : d₁ ≫ a₀ = a₁ ≫ e₁)
    (hsecond : d₂ ≫ a₁ = a₂ ≫ e₂)
    (hthird : d₃ ≫ a₂ = a₃ ≫ e₃)
    (f : DegreeTwoCocycle e₃ (Y := Y)) :
    (Ext.mk₀ g).comp
      (augmentedChainDegreeTwoToExt Q D₀ D₁ D₂ D₃ Y eta e₁ e₂ e₃
        k₁₀ k₂₁ k₃₂ kexact₀ kexact₁ kexact₂ f) (zero_add 2) =
    augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ Y epsilon d₁ d₂ d₃
      h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂
      (DegreeTwoCocycle.precompAddHom d₃ e₃ a₂ a₃ hthird f) := by
  let R := twoStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ epsilon d₁ d₂ h₁₀ h₂₁ hexact₀ hexact₁
  let S := twoStepResolutionOfAugmentedChain
    Q D₀ D₁ D₂ eta e₁ e₂ k₁₀ k₂₁ kexact₀ kexact₁
  let φ : TwoStepResolution.Hom R S :=
    TwoStepResolution.Hom.ofFirstTerms g a₀ a₁ haug (by
      change (Abelian.factorThruImage d₁ ≫ Abelian.image.ι d₁) ≫ a₀ =
        a₁ ≫ (Abelian.factorThruImage e₁ ≫ Abelian.image.ι e₁)
      rw [Abelian.image.fac, Abelian.image.fac]
      exact hfirst)
  let r : R.K₁ ⟶ Y := degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂
    (DegreeTwoCocycle.precompAddHom d₃ e₃ a₂ a₃ hthird f)
  let s : S.K₁ ⟶ Y := degreeTwoCocycleDesc e₂ e₃ k₃₂ kexact₂ f
  change (Ext.mk₀ φ.onP).comp (S.connecting Y s) (zero_add 2) = R.connecting Y r
  symm
  apply TwoStepResolution.connecting_naturality_of_coefficients φ
    (Abelian.coimage.π d₂) (Abelian.coimage.π e₂) a₂
  · change (Abelian.coimage.π d₂ ≫ Abelian.factorThruCoimage d₂) ≫ a₁ =
      a₂ ≫ (Abelian.coimage.π e₂ ≫ Abelian.factorThruCoimage e₂)
    rw [Abelian.coimage.fac, Abelian.coimage.fac]
    exact hsecond
  · change Abelian.coimage.π d₂ ≫
      degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ _ =
        a₂ ≫ (Abelian.coimage.π e₂ ≫ degreeTwoCocycleDesc e₂ e₃ k₃₂ kexact₂ f)
    rw [coimage_π_comp_degreeTwoCocycleDesc, coimage_π_comp_degreeTwoCocycleDesc]
    rfl
end PfaffianDescent
