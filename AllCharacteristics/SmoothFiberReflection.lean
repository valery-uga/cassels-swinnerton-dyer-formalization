import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Reflecting smooth fibers from a base change

A smooth base-changed family has smooth fibers over the images of its base
points. The residue-field extension at each such point is faithfully flat,
so smoothness of that fiber descends to the original residue field.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

/-- Smoothness of a base-changed family implies smoothness of the original
fiber over the image of each point of the new base. -/
theorem smooth_fiber_of_smooth_pullback
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Z ⟶ Y) (z : Z)
    [Smooth (pullback.snd f g)] :
    Smooth (f.fiberToSpecResidueField (g z)) := by
  have hs : Smooth ((pullback.snd f g).fiberToSpecResidueField z) := by
    change Smooth (pullback.snd (pullback.snd f g) (Z.fromSpecResidueField z))
    infer_instance
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth.{u}) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f g) z).flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hs

end AllCharacteristics
