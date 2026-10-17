import AllCharacteristics.AffineSchemeActionOpenDescent
import AllCharacteristics.SchemeRestrictedAction

/-!
# Stable affine neighborhoods inside invariant open subschemes

The actual affine quotient map is affine. Pulling back affine neighborhoods
inside the image of a stable open therefore gives stable affine neighborhoods
in the original scheme, with the required containment.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X Y : Scheme.{u}} (G : Type v) (ρ : G → (X ⟶ X)) (q : X ⟶ Y)

/-- The inverse image of any quotient open is stable under an invariant scheme morphism. -/
theorem schemeInvariant_preimage_stable (hq : ∀ g, ρ g ≫ q = q) (V : Y.Opens) (g : G) :
    (ρ g) ⁻¹ᵁ (q ⁻¹ᵁ V) = q ⁻¹ᵁ V := by
  ext x
  change q (ρ g x) ∈ V ↔ q x ∈ V
  have he := congrArg (fun m : X ⟶ Y ↦ m x) (hq g)
  change q (ρ g x) = q x at he
  rw [he]

variable {S : Scheme.{u}} [IsAffine X] [Group G] [Finite G]
variable (h₁ : ρ 1 = 𝟙 X) (hcomp : ∀ g h, ρ (g * h) = ρ g ≫ ρ h)
variable (f : X ⟶ S) (hf : ∀ g, ρ g ≫ f = f)

include h₁ hcomp hf in
/-- Every point of a stable open in an affine finite-group scheme action has
an actual stable affine open neighborhood contained in that open. -/
theorem exists_stable_affineOpen_inside (W : X.Opens)
    (hW : ∀ g, (ρ g) ⁻¹ᵁ W = W) (x : X) (hx : x ∈ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ W ∧ ∀ g, (ρ g) ⁻¹ᵁ U = U := by
  let Q := affineSchemeActionQuotient G ρ h₁ hcomp f hf
  let q : X ⟶ Q := affineSchemeActionQuotientMap G ρ h₁ hcomp f hf
  let V := affineSchemeActionQuotientOpen G ρ h₁ hcomp f hf W
  have hqx : q x ∈ V := ⟨x, hx, rfl⟩
  obtain ⟨V', hV', hxV', hsub⟩ := exists_isAffineOpen_mem_and_subset hqx
  refine ⟨q ⁻¹ᵁ V', hV'.preimage q, hxV', ?_, ?_⟩
  · intro y hy
    have hm : y ∈ q ⁻¹ᵁ V := hsub hy
    have he : q ⁻¹ᵁ V = W := affineSchemeActionQuotientOpen_preimage G ρ h₁ hcomp f hf W hW
    rw [he] at hm
    exact hm
  · exact schemeInvariant_preimage_stable G ρ q
      (affineSchemeActionQuotientMap_invariant G ρ h₁ hcomp f hf) V'

end AllCharacteristics
