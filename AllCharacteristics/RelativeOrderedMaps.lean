import AllCharacteristics.RelativeOrderedReindex

/-!
# Maps between actual ordered relative powers

Every morphism of families over the same base induces the coordinatewise
morphism of their ordered powers. The construction respects identities,
composition, and reindexing, with explicit head and tail formulas.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X Y Z S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
variable (a : Over.mk f ⟶ Over.mk g)

/-- Apply a morphism of families to every coordinate of the actual ordered power. -/
noncomputable def orderedFamilyMap (n : ℕ) :
    orderedFamilyPowerOver f n ⟶ orderedFamilyPowerOver g n :=
  orderedFamilyTuple g (orderedFamilyPowerOver f n) n
    (fun i ↦ orderedFamilyCoordinate f n i ≫ a)

/-- Every coordinate of the induced ordered-power morphism is the original family map. -/
theorem orderedFamilyMap_coordinate (n : ℕ) (i : Fin n) :
    orderedFamilyMap f g a n ≫ orderedFamilyCoordinate g n i =
      orderedFamilyCoordinate f n i ≫ a :=
  orderedFamilyTuple_coordinate g (orderedFamilyPowerOver f n) n _ i

/-- The ordered-power map has the prescribed first-coordinate morphism. -/
theorem orderedFamilyMap_head (n : ℕ) :
    orderedFamilyMap f g a (n + 1) ≫ orderedFamilyHead g n =
      orderedFamilyHead f n ≫ a :=
  orderedFamilyMap_coordinate f g a (n + 1) 0

/-- The tail of the ordered-power map is the induced map on the remaining coordinates. -/
theorem orderedFamilyMap_tail (n : ℕ) :
    orderedFamilyMap f g a (n + 1) ≫ orderedFamilyTail g n =
      orderedFamilyTail f n ≫ orderedFamilyMap f g a n := by
  apply orderedFamilyPower_coordinate_ext g _ n
  intro i
  rw [Category.assoc, Category.assoc, orderedFamilyMap_coordinate]
  exact (orderedFamilyMap_coordinate f g a (n + 1) i.succ).trans (Category.assoc _ _ _)

/-- Applying the identity family morphism gives the identity on the ordered power. -/
theorem orderedFamilyMap_id (n : ℕ) :
    orderedFamilyMap f f (𝟙 (Over.mk f)) n = 𝟙 (orderedFamilyPowerOver f n) := by
  apply orderedFamilyPower_coordinate_ext f _ n
  intro i
  rw [orderedFamilyMap_coordinate, Category.comp_id, Category.id_comp]

/-- Coordinatewise family maps respect actual composition. -/
theorem orderedFamilyMap_comp (h : Z ⟶ S) (b : Over.mk g ⟶ Over.mk h) (n : ℕ) :
    orderedFamilyMap f h (a ≫ b) n = orderedFamilyMap f g a n ≫ orderedFamilyMap g h b n := by
  apply orderedFamilyPower_coordinate_ext h _ n
  intro i
  rw [orderedFamilyMap_coordinate, Category.assoc, orderedFamilyMap_coordinate]
  simpa only [Category.assoc] using
    (congrArg (fun z ↦ z ≫ b) (orderedFamilyMap_coordinate f g a n i)).symm

/-- Applying the family morphism commutes with arbitrary coordinate reindexing. -/
theorem orderedFamilyMap_reindex {m n : ℕ} (ρ : Fin m → Fin n) :
    orderedFamilyMap f g a n ≫ orderedFamilyReindex g ρ =
      orderedFamilyReindex f ρ ≫ orderedFamilyMap f g a m := by
  apply orderedFamilyPower_coordinate_ext g _ m
  intro i
  rw [Category.assoc, orderedFamilyReindex_coordinate, orderedFamilyMap_coordinate,
    Category.assoc, orderedFamilyMap_coordinate, ← Category.assoc, orderedFamilyReindex_coordinate]

/-- The successor map is the actual map of pullback schemes determined by head and tail. -/
theorem orderedFamilyMap_succ_left (n : ℕ) :
    Over.Hom.left (orderedFamilyMap f g a (n + 1)) =
      pullback.map f (orderedFamilyPowerOver f n).hom g (orderedFamilyPowerOver g n).hom
        (Over.Hom.left a) (Over.Hom.left (orderedFamilyMap f g a n)) (𝟙 S)
        ((Category.comp_id f).trans a.w.symm)
        ((Category.comp_id _).trans (orderedFamilyMap f g a n).w.symm) := by
  let m : pullback f (orderedFamilyPowerOver f n).hom ⟶
      pullback g (orderedFamilyPowerOver g n).hom :=
    Over.Hom.left (orderedFamilyMap f g a (n + 1))
  change m = _
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact congrArg Over.Hom.left (orderedFamilyMap_head f g a n)
  · rw [pullback.lift_snd]
    exact congrArg Over.Hom.left (orderedFamilyMap_tail f g a n)

end AllCharacteristics
