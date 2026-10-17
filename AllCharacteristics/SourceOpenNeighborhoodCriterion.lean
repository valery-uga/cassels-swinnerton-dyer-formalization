import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Checking a source-local property on actual open neighborhoods -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- A property local on the source follows from actual open-immersion
neighborhoods of each original source point. -/
theorem property_of_source_open_neighborhoods
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ x : X, ∃ (T : Scheme.{u}) (i : T ⟶ X),
      IsOpenImmersion i ∧ x ∈ Set.range i ∧ P (i ≫ f)) : P f := by
  classical
  choose T i hi hx hP using h
  let C : X.OpenCover := {
    I₀ := X
    X := T
    f := i
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x ↦ ⟨x, hx x⟩, hi⟩ }
  exact IsZariskiLocalAtSource.of_openCover C hP

/-- Étaleness can be checked on actual open neighborhoods of every source point. -/
theorem etale_of_source_open_neighborhoods {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ x : X, ∃ (T : Scheme.{u}) (i : T ⟶ X),
      IsOpenImmersion i ∧ x ∈ Set.range i ∧ Etale (i ≫ f)) : Etale f := by
  let : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ Etale.instHasRingHomPropertyEtale
  exact property_of_source_open_neighborhoods (@Etale : MorphismProperty Scheme.{u}) f h

end AllCharacteristics
