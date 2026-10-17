import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Pullback of an open immersion over a map contained in its image

When the base-change map lands entirely in the image of an open immersion,
the corresponding pullback projection is an isomorphism. The isomorphism is
identified with the actual projection using the universal property.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- Base change inside the image of an open immersion gives an isomorphism. -/
theorem isIso_snd_of_isPullback_open_range {P X Y S : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (h : IsPullback a b f g) [IsOpenImmersion f]
    (hg : Set.range g ⊆ Set.range f) : IsIso b := by
  let h' := IsOpenImmersion.isPullback_lift_id g f hg
  let e : P ≅ Y := h.isoIsPullback X Y h'
  have he : e.hom = b := by
    simpa only [Category.comp_id] using h.isoIsPullback_hom_snd X Y h'
  rw [← he]
  infer_instance

end AllCharacteristics
