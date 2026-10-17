import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Restriction maps between successive pullback fibers

A factorization of base maps induces a canonical map of pullbacks. The
projection identities, Cartesian square, and composition law are proved.
-/

open CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe v u
variable {C : Type u} [Category.{v} C] {X S A B D : C}
variable (f : X ⟶ S) (b : A ⟶ S) (c : B ⟶ S) (a : B ⟶ A) (h : a ≫ b = c)
variable [HasPullback f b] [HasPullback f c]

/-- Restrict a pullback fiber along a factorization of its base morphism. -/
noncomputable def pullbackRestriction : pullback f c ⟶ pullback f b :=
  pullback.lift (pullback.fst f c) (pullback.snd f c ≫ a) (by
    rw [pullback.condition, Category.assoc, h])

/-- Restriction preserves the projection to the original total space. -/
theorem pullbackRestriction_fst :
    pullbackRestriction f b c a h ≫ pullback.fst f b = pullback.fst f c :=
  pullback.lift_fst _ _ _

/-- Restriction has the prescribed map on the coefficient base. -/
theorem pullbackRestriction_snd :
    pullbackRestriction f b c a h ≫ pullback.snd f b = pullback.snd f c ≫ a :=
  pullback.lift_snd _ _ _

/-- The restriction map itself is a base change along the intermediate base map. -/
theorem isPullback_pullbackRestriction :
    IsPullback (pullbackRestriction f b c a h) (pullback.snd f c) (pullback.snd f b) a := by
  apply IsPullback.of_right _ (pullbackRestriction_snd f b c a h) (IsPullback.of_hasPullback f b)
  rw [pullbackRestriction_fst, h]
  exact IsPullback.of_hasPullback f c

/-- Successive restrictions compose as their base morphisms do. -/
theorem pullbackRestriction_comp (e : D ⟶ S) (a' : D ⟶ B) (h' : a' ≫ c = e)
    [HasPullback f e] :
    pullbackRestriction f c e a' h' ≫ pullbackRestriction f b c a h =
      pullbackRestriction f b e (a' ≫ a) (by rw [Category.assoc, h, h']) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackRestriction_fst]
  · rw [Category.assoc, pullbackRestriction_snd, ← Category.assoc,
      pullbackRestriction_snd, pullbackRestriction_snd, Category.assoc]

end AllCharacteristics
