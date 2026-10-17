import AllCharacteristics.SchemeRestrictedAction

/-! # Equivariance under actual restriction to an invariant target open -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X Y : Scheme.{u}} (G : Type v)
variable (ρX : G → (X ⟶ X)) (ρY : G → (Y ⟶ Y))
variable (c : X ⟶ Y) (hc : ∀ g, ρX g ≫ c = c ≫ ρY g)
variable (U : Y.Opens) (hU : ∀ g, (ρY g) ⁻¹ᵁ U = U)

include hc hU in
/-- An equivariant morphism pulls a stable open back to a stable open. -/
theorem equivariant_preimage_open_stable (g : G) :
    (ρX g) ⁻¹ᵁ (c ⁻¹ᵁ U) = c ⁻¹ᵁ U := by
  ext x
  change c (ρX g x) ∈ U ↔ c x ∈ U
  have he := congrArg (fun m : X ⟶ Y ↦ m x) (hc g)
  change c (ρX g x) = ρY g (c x) at he
  rw [he]
  change c x ∈ (ρY g) ⁻¹ᵁ U ↔ c x ∈ U
  rw [hU g]

/-- The actual restriction morphism is equivariant for the pulled-back action
and any target-open action with the prescribed original inclusion. -/
theorem equivariant_morphismRestrict
    (τ : G → (U.toScheme ⟶ U.toScheme)) (hτ : ∀ g, τ g ≫ U.ι = U.ι ≫ ρY g) (g : G) :
    schemeRestrictedRightAction G ρX (c ⁻¹ᵁ U)
      (equivariant_preimage_open_stable G ρX ρY c hc U hU) g ≫ (c ∣_ U) =
        (c ∣_ U) ≫ τ g := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
    schemeRestrictedRightAction_ι, Category.assoc, hc,
    Category.assoc, hτ]
  rw [← Category.assoc (c ∣_ U), morphismRestrict_ι, Category.assoc]

end AllCharacteristics
