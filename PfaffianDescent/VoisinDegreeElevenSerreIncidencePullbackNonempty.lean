import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Literal nonempty base change along a surjective morphism -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem serreIncidencePullback_nonempty
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [Nonempty X] [Surjective g] : Nonempty (pullback f g : Scheme.{u}) := by
  obtain ⟨z,hz⟩ := (pullback.fst f g).surjective (Classical.choice (inferInstance : Nonempty X))
  exact ⟨z⟩

end PfaffianDescent
