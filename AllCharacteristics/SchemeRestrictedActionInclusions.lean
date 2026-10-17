import AllCharacteristics.SchemeRestrictedAction

/-!
# Equivariance of inclusions between stable open subschemes

The actual inclusions between stable opens commute with the restricted
scheme actions and with the original structure morphism. These identities
supply the input for morphisms between the corresponding quotient charts.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X S : Scheme.{u}} (G : Type v) (ρ : G → (X ⟶ X))
variable (U V : X.Opens) (hU : ∀ g : G, (ρ g) ⁻¹ᵁ U = U)
variable (hV : ∀ g : G, (ρ g) ⁻¹ᵁ V = V) (hUV : U ≤ V)

/-- The actual inclusion between stable opens is equivariant for their restricted actions. -/
theorem schemeRestrictedRightAction_homOfLE (g : G) :
    schemeRestrictedRightAction G ρ U hU g ≫ X.homOfLE hUV =
      X.homOfLE hUV ≫ schemeRestrictedRightAction G ρ V hV g := by
  apply (cancel_mono V.ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι, schemeRestrictedRightAction_ι,
    Category.assoc, schemeRestrictedRightAction_ι, ← Category.assoc, Scheme.homOfLE_ι]

/-- Inclusion of actual open subfamilies retains the original structure morphism. -/
theorem homOfLE_toBase (f : X ⟶ S) :
    X.homOfLE hUV ≫ (V.ι ≫ f) = U.ι ≫ f := by
  rw [← Category.assoc, Scheme.homOfLE_ι]

end AllCharacteristics
