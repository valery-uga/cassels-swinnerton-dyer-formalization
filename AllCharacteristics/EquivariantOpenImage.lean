import AllCharacteristics.SchemeRestrictedAction

/-!
# Stability of the image of an equivariant open immersion

Equivariance and the target action's inverse law show that the image of an
open immersion is stable. This turns coordinatewise common-open embeddings
into actual stable opens for the symmetric-group action.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X Y : Scheme.{u}} (G : Type v) [Group G]
variable (ρ : G → (Y ⟶ Y)) (h₁ : ρ 1 = 𝟙 Y)
variable (hcomp : ∀ g h : G, ρ (g * h) = ρ g ≫ ρ h)
variable (τ : G → (X ⟶ X)) (a : X ⟶ Y) [IsOpenImmersion a]
variable (ha : ∀ g : G, τ g ≫ a = a ≫ ρ g)

include h₁ hcomp ha in
/-- The actual image open of an equivariant open immersion is stable under the group action. -/
theorem equivariant_opensRange_preimage (g : G) :
    (ρ g) ⁻¹ᵁ a.opensRange = a.opensRange := by
  ext y
  change ρ g y ∈ Set.range a ↔ y ∈ Set.range a
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨τ g⁻¹ x, ?_⟩
    have ht := congrArg (fun z : X ⟶ Y ↦ z x) (ha g⁻¹)
    change a (τ g⁻¹ x) = ρ g⁻¹ (a x) at ht
    rw [ht, hx]
    have hi : ρ g ≫ ρ g⁻¹ = 𝟙 Y := by
      rw [← hcomp, mul_inv_cancel, h₁]
    exact congrArg (fun z : Y ⟶ Y ↦ z y) hi
  · rintro ⟨x, rfl⟩
    refine ⟨τ g x, ?_⟩
    exact congrArg (fun z : X ⟶ Y ↦ z x) (ha g)

end AllCharacteristics
