import PfaffianDescent.ResolutionCoefficientExtension
import PfaffianDescent.CechExtDegreeThree
import PfaffianDescent.CechExtDegreeTwo

/-! # The actual coefficient connecting map on Cech cocycles -/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w
variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

set_option backward.isDefEq.respectTransparency false in
/-- Lifting a degree-two cocycle through a coefficient extension and taking
its differential computes the actual Ext connecting class, including its sign. -/
theorem augmentedChainDegreeTwoToExt_comp_coefficient_extension
    (P C₀ C₁ C₂ C₃ C₄ : A)
    (ε : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₁₀ : d₁ ≫ ε = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0) (h₄₃ : d₄ ≫ d₃ = 0)
    (hexact₀ : (ShortComplex.mk d₁ ε h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact)
    [Epi ε] (S : ShortComplex A) (hS : S.ShortExact)
    (z : DegreeTwoCocycle d₃ (Y := S.X₃)) (l : C₂ ⟶ S.X₂)
    (a : DegreeThreeCocycle d₄ (Y := S.X₁))
    (hl : l ≫ S.g = z.1) (ha : d₃ ≫ l = a.1 ≫ S.f) :
    (augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ S.X₃
      ε d₁ d₂ d₃ h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ z).comp
      hS.extClass (show 2 + 1 = 3 by rfl) =
    augmentedChainDegreeThreeToExt P C₀ C₁ C₂ C₃ C₄ S.X₁
      ε d₁ d₂ d₃ d₄ h₁₀ h₂₁ h₃₂ h₄₃ hexact₀ hexact₁ hexact₂ hexact₃ a := by
  let R := threeStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ C₃ ε d₁ d₂ d₃ h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂
  let φ := degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ z
  let ψ := degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ a
  have hleft : R.i₂ ≫ l = ψ ≫ S.f := by
    apply (cancel_epi (Abelian.coimage.π d₃)).1
    change Abelian.coimage.π d₃ ≫ (Abelian.factorThruCoimage d₃ ≫ l) =
      Abelian.coimage.π d₃ ≫ (degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ a ≫ S.f)
    rw [← Category.assoc, Abelian.coimage.fac, ← Category.assoc,
      coimage_π_comp_degreeThreeCocycleDesc]
    exact ha
  have hright : R.p₂ ≫ φ = l ≫ S.g :=
    (coimage_π_comp_degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ z).trans hl.symm
  exact R.prefix_connecting_comp_coefficient_extension S hS φ l ψ hleft hright
end PfaffianDescent
