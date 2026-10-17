import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Field-valued points of open subschemes

A morphism from the spectrum of a field factors through an open immersion
exactly when its unique underlying point lies in the image. The factorization
uses the original field and the original morphism.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u

/-- Membership of a field-valued point in an open image gives a lift over exactly that field. -/
theorem fieldPoint_mem_open_range_iff {Z X : Scheme.{u}} (i : Z ⟶ X) [IsOpenImmersion i]
    {k : Type u} [Field k] (a : Spec (.of k) ⟶ X) :
    a (IsLocalRing.closedPoint k) ∈ Set.range i ↔
      ∃ b : Spec (.of k) ⟶ Z, b ≫ i = a := by
  constructor
  · intro h
    have hr : Set.range a ⊆ Set.range i := by
      rintro _ ⟨x, rfl⟩
      simpa only [Subsingleton.elim x (IsLocalRing.closedPoint k)] using h
    exact ⟨IsOpenImmersion.lift i a hr, IsOpenImmersion.lift_fac i a hr⟩
  · rintro ⟨b, hb⟩
    exact ⟨b (IsLocalRing.closedPoint k), congrArg (fun f ↦ f (IsLocalRing.closedPoint k)) hb⟩

end AllCharacteristics
