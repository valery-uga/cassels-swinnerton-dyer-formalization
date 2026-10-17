import AllCharacteristics.StableAffineNeighborhoods
import AllCharacteristics.SourceOpenNeighborhoodCriterion
import AllCharacteristics.SchemeRestrictedActionInclusions
import AllCharacteristics.AffineSchemeFreeAction
import AllCharacteristics.AffineSchemeQuotientOpenImmersion

/-! # Étaleness on a free stable open of an actual affine quotient -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {X S : Scheme.{u}} [IsAffine X] (G : Type v) [Group G] [Finite G]
variable (ρ : G → (X ⟶ X)) (h₁ : ρ 1 = 𝟙 X)
variable (hcomp : ∀ g h, ρ (g * h) = ρ g ≫ ρ h)
variable (f : X ⟶ S) (hf : ∀ g, ρ g ≫ f = f)
variable (W : X.Opens) (hW : ∀ g, (ρ g) ⁻¹ᵁ W = W)

/-- The actual affine quotient is étale on any stable open where the original
restricted action is free on field-valued points. -/
theorem etale_affineSchemeActionQuotientMap_on_free_open
    (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ W.toScheme) (g : G),
      g ≠ 1 → a ≫ schemeRestrictedRightAction G ρ W hW g ≠ a) :
    Etale (W.ι ≫ affineSchemeActionQuotientMap G ρ h₁ hcomp f hf) := by
  apply etale_of_source_open_neighborhoods
  intro x
  obtain ⟨U, hUa, hxU, hUW, hU⟩ :=
    exists_stable_affineOpen_inside G ρ h₁ hcomp f hf W hW x.val x.property
  have : IsAffine U.toScheme := hUa
  let τ := schemeRestrictedRightAction G ρ U hU
  have ht₁ : τ 1 = 𝟙 U.toScheme := schemeRestrictedRightAction_one G ρ h₁ U hU
  have htcomp : ∀ g h, τ (g * h) = τ g ≫ τ h :=
    schemeRestrictedRightAction_mul G ρ hcomp U hU
  let p : U.toScheme ⟶ S := U.ι ≫ f
  have hp : ∀ g, τ g ≫ p = p := schemeRestrictedRightAction_toBase G ρ U hU f hf
  have ha : ∀ g, τ g ≫ U.ι = U.ι ≫ ρ g := schemeRestrictedRightAction_ι G ρ U hU
  let qU := affineSchemeActionQuotientMap G τ ht₁ htcomp p hp
  have hqU : Etale qU := by
    apply etale_affineSchemeActionQuotientMap_of_free G τ ht₁ htcomp p hp
    intro K _ a g hg he
    apply hfree K (a ≫ X.homOfLE hUW) g hg
    rw [Category.assoc, ← schemeRestrictedRightAction_homOfLE G ρ U W hU hW hUW,
      ← Category.assoc]
    exact congrArg (fun m ↦ m ≫ X.homOfLE hUW) he
  let j := affineSchemeActionQuotientMorphism G τ ht₁ htcomp ρ h₁ hcomp p hp f hf U.ι ha
  have hj : IsOpenImmersion j :=
    isOpenImmersion_affineSchemeActionQuotientMorphism G τ ht₁ htcomp ρ h₁ hcomp p hp f hf U.ι ha
  have hjq : qU ≫ j = U.ι ≫ affineSchemeActionQuotientMap G ρ h₁ hcomp f hf :=
    affineSchemeActionQuotientMorphism_square G τ ht₁ htcomp ρ h₁ hcomp p hp f hf U.ι ha
  refine ⟨U.toScheme, X.homOfLE hUW, inferInstance, ?_, ?_⟩
  · refine ⟨⟨x.val, hxU⟩, ?_⟩
    apply Subtype.ext
    exact Scheme.homOfLE_apply hUW ⟨x.val, hxU⟩
  · rw [← Category.assoc, Scheme.homOfLE_ι, ← hjq]
    infer_instance

end AllCharacteristics
