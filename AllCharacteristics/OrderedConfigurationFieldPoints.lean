import AllCharacteristics.RelativeConfigurationPermutations

/-!
# Field-valued points of ordered configuration spaces

A pairwise-distinct tuple of field-valued points in one fiber determines an
actual morphism to the ordered configuration scheme.  The construction is
made through the universal property of the relative ordered power and the
proved field-point criterion for the complement of the diagonals.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (n : ℕ)

/-- Different labels of a field-valued ordered configuration give distinct
morphisms to the original family. -/
theorem orderedConfigurationFieldPoint_coordinates_ne
    {k : Type u} [Field k]
    (a : Spec (.of k) ⟶ (orderedFamilyConfigurationOver f n).left)
    (i j : Fin n) (hij : i ≠ j) :
    (a ≫ (orderedFamilyConfigurationOpen f n).ι) ≫
        (orderedFamilyCoordinate f n i).left ≠
      (a ≫ (orderedFamilyConfigurationOpen f n).ι) ≫
        (orderedFamilyCoordinate f n j).left := by
  let b := a ≫ (orderedFamilyConfigurationOver f n).hom
  let A : Over.mk b ⟶ orderedFamilyConfigurationOver f n :=
    Over.homMk a rfl
  have ha : Over.Hom.left (A ≫ orderedFamilyConfigurationι f n)
      (IsLocalRing.closedPoint k) ∈ orderedFamilyConfigurationOpen f n := by
    change (orderedFamilyConfigurationOpen f n).ι
      (a (IsLocalRing.closedPoint k)) ∈ orderedFamilyConfigurationOpen f n
    exact (a (IsLocalRing.closedPoint k)).2
  have hc := (fieldTuple_mem_configuration_iff f n b
    (A ≫ orderedFamilyConfigurationι f n)).mp ha
  intro he
  apply hc i j hij
  apply Over.OverMorphism.ext
  change (a ≫ (orderedFamilyConfigurationOpen f n).ι) ≫
      (orderedFamilyCoordinate f n i).left =
    (a ≫ (orderedFamilyConfigurationOpen f n).ι) ≫
      (orderedFamilyCoordinate f n j).left
  exact he

/-- Distinct ordered coordinates stay distinct after any monomorphism of
the original family into another scheme. -/
theorem orderedConfigurationFieldPoint_coordinates_comp_injective
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (g : X ⟶ Y) [Mono g]
    (a : Spec (.of k) ⟶ (orderedFamilyConfigurationOver f n).left) :
    Function.Injective (fun i : Fin n =>
      ((a ≫ (orderedFamilyConfigurationOpen f n).ι) ≫
        (orderedFamilyCoordinate f n i).left) ≫ g) := by
  intro i j hij
  by_contra hne
  exact orderedConfigurationFieldPoint_coordinates_ne f n a i j hne
    ((cancel_mono g).mp hij)

/-- A pairwise-distinct tuple in one field-valued fiber gives a point of the
actual ordered configuration scheme, with exactly the prescribed
coordinates. -/
theorem exists_orderedConfigurationFieldPoint
    {k : Type u} [Field k] (b : Spec (.of k) ⟶ S)
    (q : Fin n → (Spec (.of k) ⟶ X))
    (hq : ∀ i, q i ≫ f = b)
    (hdist : ∀ i j, i ≠ j → q i ≠ q j) :
    ∃ a : Spec (.of k) ⟶ (orderedFamilyConfigurationOver f n).left,
      a ≫ (orderedFamilyConfigurationOver f n).hom = b ∧
      ∀ i, (a ≫ Over.Hom.left (orderedFamilyConfigurationι f n)) ≫
        (orderedFamilyCoordinate f n i).left = q i := by
  let s : Fin n → (Over.mk b ⟶ Over.mk f) := fun i ↦ Over.homMk (q i) (hq i)
  let t : Over.mk b ⟶ orderedFamilyPowerOver f n := orderedFamilyTuple f (Over.mk b) n s
  have ht : t.left (IsLocalRing.closedPoint k) ∈ orderedFamilyConfigurationOpen f n := by
    apply (fieldTuple_mem_configuration_iff f n b t).mpr
    intro i j hij
    rw [orderedFamilyTuple_coordinate, orderedFamilyTuple_coordinate]
    intro he
    exact hdist i j hij (congrArg Over.Hom.left he)
  let r : Spec (.of k) ⟶ (orderedFamilyPowerOver f n).left := t.left
  have hrange : Set.range r ⊆ Set.range (orderedFamilyConfigurationOpen f n).ι := by
    rintro y ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    subst z
    exact ⟨⟨r (IsLocalRing.closedPoint k), by exact ht⟩, rfl⟩
  let a : Spec (.of k) ⟶ (orderedFamilyConfigurationOver f n).left := by
    change Spec (.of k) ⟶ (orderedFamilyConfigurationOpen f n).toScheme
    exact IsOpenImmersion.lift (orderedFamilyConfigurationOpen f n).ι r hrange
  have haι : a ≫ Over.Hom.left (orderedFamilyConfigurationι f n) = r := by
    change
      IsOpenImmersion.lift (orderedFamilyConfigurationOpen f n).ι r hrange ≫
        (orderedFamilyConfigurationOpen f n).ι = r
    exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨a, ?_, ?_⟩
  · rw [← (orderedFamilyConfigurationι f n).w, ← Category.assoc, haι]
    change t.left ≫ (orderedFamilyPowerOver f n).hom = b
    exact t.w
  · intro i
    rw [haι]
    change t.left ≫ (orderedFamilyCoordinate f n i).left = q i
    exact congrArg Over.Hom.left (orderedFamilyTuple_coordinate f (Over.mk b) n s i)

/-- Two field-valued points of an ordered configuration in the same fiber
are equal once all of their marked coordinates agree. -/
theorem orderedConfigurationFieldPoint_ext
    {k : Type u} [Field k] (b : Spec (.of k) ⟶ S)
    {a a' : Spec (.of k) ⟶ (orderedFamilyConfigurationOver f n).left}
    (ha : a ≫ (orderedFamilyConfigurationOver f n).hom = b)
    (ha' : a' ≫ (orderedFamilyConfigurationOver f n).hom = b)
    (hcoordinate : ∀ i,
      (a ≫ Over.Hom.left (orderedFamilyConfigurationι f n)) ≫
          (orderedFamilyCoordinate f n i).left =
        (a' ≫ Over.Hom.left (orderedFamilyConfigurationι f n)) ≫
          (orderedFamilyCoordinate f n i).left) :
    a = a' := by
  apply (cancel_mono (Over.Hom.left (orderedFamilyConfigurationι f n))).mp
  let A : Over.mk b ⟶ orderedFamilyConfigurationOver f n := Over.homMk a ha
  let A' : Over.mk b ⟶ orderedFamilyConfigurationOver f n := Over.homMk a' ha'
  have h : A ≫ orderedFamilyConfigurationι f n = A' ≫ orderedFamilyConfigurationι f n := by
    apply orderedFamilyPower_coordinate_ext f (Over.mk b) n
    intro i
    apply Over.OverMorphism.ext
    change a ≫ Over.Hom.left (orderedFamilyConfigurationι f n) ≫
        (orderedFamilyCoordinate f n i).left =
      a' ≫ Over.Hom.left (orderedFamilyConfigurationι f n) ≫
        (orderedFamilyCoordinate f n i).left
    simpa only [Category.assoc] using hcoordinate i
  exact congrArg Over.Hom.left h

/-- Deleting one coordinate from an ordered field-valued configuration gives
the prescribed smaller configuration when all retained marked coordinates
agree. -/
theorem orderedConfigurationDelete_fieldPoint_eq
    {k : Type u} [Field k] (b : Spec (.of k) ⟶ S)
    {a : Spec (.of k) ⟶ (orderedFamilyConfigurationOver f (n + 1)).left}
    {a' : Spec (.of k) ⟶ (orderedFamilyConfigurationOver f n).left}
    (ha : a ≫ (orderedFamilyConfigurationOver f (n + 1)).hom = b)
    (ha' : a' ≫ (orderedFamilyConfigurationOver f n).hom = b)
    (i : Fin (n + 1))
    (hcoordinate : ∀ j,
      ((a ≫ Over.Hom.left (orderedFamilyConfigurationDelete f n i)) ≫
        Over.Hom.left (orderedFamilyConfigurationι f n)) ≫
          (orderedFamilyCoordinate f n j).left =
        (a' ≫ Over.Hom.left (orderedFamilyConfigurationι f n)) ≫
          (orderedFamilyCoordinate f n j).left) :
    a ≫ Over.Hom.left (orderedFamilyConfigurationDelete f n i) = a' := by
  apply orderedConfigurationFieldPoint_ext f n b ?_ ha' hcoordinate
  calc
    (a ≫ Over.Hom.left (orderedFamilyConfigurationDelete f n i)) ≫
        (orderedFamilyConfigurationOver f n).hom =
      a ≫ (Over.Hom.left (orderedFamilyConfigurationDelete f n i) ≫
        (orderedFamilyConfigurationOver f n).hom) := Category.assoc _ _ _
    _ = a ≫ (orderedFamilyConfigurationOver f (n + 1)).hom := by
      rw [(orderedFamilyConfigurationDelete f n i).w]
    _ = b := ha

end AllCharacteristics
