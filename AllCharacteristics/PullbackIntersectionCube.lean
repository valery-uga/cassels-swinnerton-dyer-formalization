import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# A Cartesian intersection cube

Two Cartesian faces and a Cartesian base intersection identify the upper
intersection. This elementary pasting lemma will identify the actual
universal triple hypersurface with the pullback of two overlap families.
-/

open CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe v u
variable {C : Type u} [Category.{v} C]

/-- Cartesian restriction over a base intersection gives the corresponding
Cartesian intersection of the two upper families. -/
theorem isPullback_intersection_cube {W V₁ V₂ U T B₁ B₂ B : C}
    (a : W ⟶ V₁) (b : W ⟶ V₂) (c : V₁ ⟶ U) (d : V₂ ⟶ U)
    (x : W ⟶ T) (y : V₁ ⟶ B₁) (z : V₂ ⟶ B₂) (u : U ⟶ B)
    (α : T ⟶ B₁) (β : T ⟶ B₂) (l : B₁ ⟶ B) (m : B₂ ⟶ B)
    (hW : IsPullback a x y α) (hB : IsPullback α β l m) (hV : IsPullback d z u m)
    (hx : b ≫ z = x ≫ β) (hy : c ≫ u = y ≫ l) (hab : a ≫ c = b ≫ d) :
    IsPullback a b c d := by
  have h := hW.paste_vert hB
  rw [← hx, ← hy] at h
  exact h.of_bot hab hV

end AllCharacteristics
