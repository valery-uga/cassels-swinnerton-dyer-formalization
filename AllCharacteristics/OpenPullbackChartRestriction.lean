import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Restricting an actual quotient chart through an open pullback square -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X Y U V W Z : Scheme.{u}}
variable (q : X ⟶ Y) (r : U ⟶ V) [Surjective r]
variable (i : U ⟶ X) [IsOpenImmersion i] (j : V ⟶ Y) [IsOpenImmersion j]
variable (l : W ⟶ X) [IsOpenImmersion l] (k : Z ⟶ Y) [IsOpenImmersion k]
variable (s : W ⟶ Z)

/-- A quotient chart whose source lies in an open pullback square restricts to
an actual open quotient chart in that square, with both inclusions identified. -/
theorem exists_openPullbackChart_restriction (hp : IsPullback i r q j)
    (hw : IsPullback l s q k) (hi : Set.range i ⊆ Set.range l) :
    ∃ (a : U ⟶ W) (b : V ⟶ Z),
      a ≫ l = i ∧ b ≫ k = j ∧ IsOpenImmersion a ∧ IsOpenImmersion b ∧
        IsPullback a r s b := by
  let a := IsOpenImmersion.lift l i hi
  have ha : a ≫ l = i := IsOpenImmersion.lift_fac l i hi
  have hj : Set.range j ⊆ Set.range k := by
    rintro y ⟨v, rfl⟩
    obtain ⟨u, rfl⟩ := r.surjective v
    refine ⟨s (a u), ?_⟩
    have he : (a ≫ s) ≫ k = r ≫ j := by
      rw [Category.assoc, ← hw.w, ← Category.assoc, ha, hp.w]
    exact congrArg (fun m : U ⟶ Y ↦ m u) he
  let b := IsOpenImmersion.lift k j hj
  have hb : b ≫ k = j := IsOpenImmersion.lift_fac k j hj
  have hsq : a ≫ s = r ≫ b := by
    apply (cancel_mono k).mp
    rw [Category.assoc, ← hw.w, ← Category.assoc, ha,
      Category.assoc, hb, hp.w]
  refine ⟨a, b, ha, hb, inferInstance, inferInstance, ?_⟩
  have hbig : IsPullback (a ≫ l) r q (b ≫ k) := by rw [ha, hb]; exact hp
  exact hbig.of_right hsq hw

end AllCharacteristics
