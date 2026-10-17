import PfaffianDescent.ResolutionCoefficientExtension
import PfaffianDescent.CechExtDegreeTwo
import PfaffianDescent.DegreeThreeResolutionNaturality

/-! # Coefficient boundaries on a bounded source complex

This is a Yoneda statement, proved by naturality of the three actual short
exact sequences extracted from the source complex. It makes no trace or
Gysin compatibility assumption.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace PfaffianDescent

universe u v w

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- Lifting a degree-two cocycle through a coefficient extension computes
its Yoneda boundary by the induced degree-three cocycle. -/
theorem pointCartierYoneda_cocycle_boundary
    (P C₀ C₁ C₂ C₃ C₄ : A)
    (epsilon : C₀ ⟶ P) (d₁ : C₁ ⟶ C₀) (d₂ : C₂ ⟶ C₁)
    (d₃ : C₃ ⟶ C₂) (d₄ : C₄ ⟶ C₃)
    (h₁₀ : d₁ ≫ epsilon = 0) (h₂₁ : d₂ ≫ d₁ = 0)
    (h₃₂ : d₃ ≫ d₂ = 0) (h₄₃ : d₄ ≫ d₃ = 0)
    (hexact₀ : (ShortComplex.mk d₁ epsilon h₁₀).Exact)
    (hexact₁ : (ShortComplex.mk d₂ d₁ h₂₁).Exact)
    (hexact₂ : (ShortComplex.mk d₃ d₂ h₃₂).Exact)
    (hexact₃ : (ShortComplex.mk d₄ d₃ h₄₃).Exact)
    [Epi epsilon]
    (S : ShortComplex A) (hS : S.ShortExact)
    (f : DegreeTwoCocycle d₃ (Y := S.X₃))
    (l : C₂ ⟶ S.X₂) (g : DegreeThreeCocycle d₄ (Y := S.X₁))
    (hl : l ≫ S.g = f.1) (hg : d₃ ≫ l = g.1 ≫ S.f) :
    (augmentedChainDegreeTwoToExt P C₀ C₁ C₂ C₃ S.X₃
        epsilon d₁ d₂ d₃ h₁₀ h₂₁ h₃₂ hexact₀ hexact₁ hexact₂ f).comp
        hS.extClass (show 2 + 1 = 3 by rfl) =
      augmentedChainDegreeThreeToExt P C₀ C₁ C₂ C₃ C₄ S.X₁
        epsilon d₁ d₂ d₃ d₄ h₁₀ h₂₁ h₃₂ h₄₃
        hexact₀ hexact₁ hexact₂ hexact₃ g := by
  let R := threeStepResolutionOfAugmentedChain
    P C₀ C₁ C₂ C₃ epsilon d₁ d₂ d₃ h₁₀ h₂₁ h₃₂
      hexact₀ hexact₁ hexact₂
  let φ : R.K₁ ⟶ S.X₃ := degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f
  let ψ : R.K₂ ⟶ S.X₁ := degreeThreeCocycleDesc d₃ d₄ h₄₃ hexact₃ g
  have hleft : R.i₂ ≫ l = ψ ≫ S.f := by
    apply (cancel_epi (Abelian.coimage.π d₃)).1
    change Abelian.coimage.π d₃ ≫ (Abelian.factorThruCoimage d₃ ≫ l) =
      Abelian.coimage.π d₃ ≫ (ψ ≫ S.f)
    rw [← Category.assoc, Abelian.coimage.fac, ← Category.assoc,
      coimage_π_comp_degreeThreeCocycleDesc]
    exact hg
  have hright : R.p₂ ≫ φ = l ≫ S.g := by
    change Abelian.coimage.π d₂ ≫
      degreeTwoCocycleDesc d₂ d₃ h₃₂ hexact₂ f = l ≫ S.g
    rw [coimage_π_comp_degreeTwoCocycleDesc]
    exact hl.symm
  exact R.prefix_connecting_comp_coefficient_extension S hS φ l ψ hleft hright

end PfaffianDescent
