import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # TargetOpenNeighborhoodCriterion

A target-local morphism property can be checked on actual open-immersion neighborhoods. In particular, a morphism is an isomorphism when these original base changes are isomorphisms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

theorem property_of_target_open_neighborhoods
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ y : Y, ∃ (T : Scheme.{u}) (i : T ⟶ Y),
      IsOpenImmersion i ∧ y ∈ Set.range i ∧ P (pullback.snd f i)) : P f := by
  classical
  choose T i hi hy hP using h
  let C : Y.OpenCover := {
    I₀ := Y
    X := T
    f := i
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun y ↦ ⟨y, hy y⟩, hi⟩ }
  exact IsZariskiLocalAtTarget.of_openCover C hP

theorem isIso_of_target_open_neighborhoods
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ y : Y, ∃ (T : Scheme.{u}) (i : T ⟶ Y),
      IsOpenImmersion i ∧ y ∈ Set.range i ∧ IsIso (pullback.snd f i)) : IsIso f := by
  let : IsZariskiLocalAtTarget (MorphismProperty.isomorphisms Scheme.{u}) :=
    @HasAffineProperty.instIsZariskiLocalAtTarget _ _
      AlgebraicGeometry.instHasAffinePropertyIsomorphismsSchemeAndIsAffineIsIsoCommRingCatAppTop
  exact property_of_target_open_neighborhoods (MorphismProperty.isomorphisms Scheme.{u}) f h

end AllCharacteristics
