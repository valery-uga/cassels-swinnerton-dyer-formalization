import AllCharacteristics.RelativeOrderedPowers

/-!
# The universal property of ordered relative powers

Maps to the iterated fiber product are exactly ordered tuples of maps to the
original family over the same base. Both directions and their inverse laws
are proved for actual scheme morphisms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (T : Over S)

/-- Construct the morphism to the ordered power from a tuple over the base. -/
noncomputable def orderedFamilyTuple : (n : ℕ) →
    (Fin n → (T ⟶ Over.mk f)) → (T ⟶ orderedFamilyPowerOver f n)
  | 0, _ => Over.homMk T.hom (Category.comp_id _)
  | n + 1, s => by
    let t := orderedFamilyTuple n (fun j ↦ s j.succ)
    refine Over.homMk (pullback.lift (s 0).left t.left ((s 0).w.trans t.w.symm)) ?_
    change pullback.lift (s 0).left t.left _ ≫
      (pullback.fst f (orderedFamilyPowerOver f n).hom ≫ f) = T.hom
    rw [← Category.assoc, pullback.lift_fst]
    exact (s 0).w

/-- The universal tuple construction has the specified first component. -/
theorem orderedFamilyTuple_head (n : ℕ) (s : Fin (n + 1) → (T ⟶ Over.mk f)) :
    orderedFamilyTuple f T (n + 1) s ≫ orderedFamilyHead f n = s 0 := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst _ _ _

/-- The universal tuple construction has the specified remaining tuple. -/
theorem orderedFamilyTuple_tail (n : ℕ) (s : Fin (n + 1) → (T ⟶ Over.mk f)) :
    orderedFamilyTuple f T (n + 1) s ≫ orderedFamilyTail f n =
      orderedFamilyTuple f T n (fun j ↦ s j.succ) := by
  apply Over.OverMorphism.ext
  exact pullback.lift_snd _ _ _

/-- Every coordinate of the constructed relative tuple is the original map. -/
theorem orderedFamilyTuple_coordinate (n : ℕ) (s : Fin n → (T ⟶ Over.mk f)) (i : Fin n) :
    orderedFamilyTuple f T n s ≫ orderedFamilyCoordinate f n i = s i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact orderedFamilyTuple_head f T n s
    · change orderedFamilyTuple f T (n + 1) s ≫
        (orderedFamilyTail f n ≫ orderedFamilyCoordinate f n j) = s j.succ
      rw [← Category.assoc, orderedFamilyTuple_tail]
      exact ih _ _

/-- Maps to an ordered relative power are determined by all their coordinates. -/
theorem orderedFamilyPower_coordinate_ext (n : ℕ)
    {a b : T ⟶ orderedFamilyPowerOver f n}
    (h : ∀ i, a ≫ orderedFamilyCoordinate f n i = b ≫ orderedFamilyCoordinate f n i) :
    a = b := by
  induction n with
  | zero => exact Over.mkIdTerminal.hom_ext a b
  | succ n ih =>
    apply orderedFamilyPower_hom_ext f n
    · exact h 0
    · apply ih
      intro j
      exact (Category.assoc _ _ _).trans ((h j.succ).trans (Category.assoc _ _ _).symm)

/-- Reconstructing a map from its coordinate tuple recovers the original map. -/
theorem orderedFamilyTuple_coordinates (n : ℕ) (a : T ⟶ orderedFamilyPowerOver f n) :
    orderedFamilyTuple f T n (fun i ↦ a ≫ orderedFamilyCoordinate f n i) = a := by
  apply orderedFamilyPower_coordinate_ext f T n
  intro i
  exact orderedFamilyTuple_coordinate f T n _ i

/-- The actual ordered fiber power represents tuples of maps over the base. -/
noncomputable def orderedFamilyTupleEquiv (n : ℕ) :
    (T ⟶ orderedFamilyPowerOver f n) ≃ (Fin n → (T ⟶ Over.mk f)) where
  toFun a i := a ≫ orderedFamilyCoordinate f n i
  invFun := orderedFamilyTuple f T n
  left_inv := orderedFamilyTuple_coordinates f T n
  right_inv s := funext (orderedFamilyTuple_coordinate f T n s)

end AllCharacteristics
