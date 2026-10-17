import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Field-valued points on closed subschemes

A field-valued point factors through a closed immersion exactly when its
underlying point belongs to the closed image. The proof retains the original
field and uses the fact that a surjective closed immersion into a reduced
scheme is an isomorphism.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
variable {k : Type u} [Field k] (a : Spec (.of k) ⟶ X)

/-- Membership of a field-valued point in a closed image is equivalent to
factorization over the same field. -/
theorem fieldPoint_mem_closed_range_iff :
    a (IsLocalRing.closedPoint k) ∈ Set.range i ↔
      ∃ b : Spec (.of k) ⟶ Z, b ≫ i = a := by
  constructor
  · intro h
    have : Surjective (pullback.fst a i) := by
      constructor
      intro x
      have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      have hr : x ∈ Set.range (pullback.fst a i) := by
        rw [Scheme.Pullback.range_fst]
        change a x ∈ Set.range i
        rw [hx]
        exact h
      exact hr
    have : IsIso (pullback.fst a i) :=
      isIso_of_isClosedImmersion_of_surjective (pullback.fst a i)
    refine ⟨inv (pullback.fst a i) ≫ pullback.snd a i, ?_⟩
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  · rintro ⟨b, hb⟩
    refine ⟨b (IsLocalRing.closedPoint k), ?_⟩
    exact congrArg (fun c : Spec (.of k) ⟶ X ↦ c (IsLocalRing.closedPoint k)) hb

end AllCharacteristics
