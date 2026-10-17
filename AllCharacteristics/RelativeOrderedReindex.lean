import AllCharacteristics.RelativeOrderedTuples

/-!
# Reindexing actual ordered relative powers

Every map of finite coordinate sets induces a morphism of the representing
schemes. Identity and composition hold for the actual morphisms, and coordinate
permutations give actual scheme isomorphisms over the original base.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Reindex an ordered relative tuple by a map of coordinate sets. -/
noncomputable def orderedFamilyReindex {m n : ℕ} (ρ : Fin m → Fin n) :
    orderedFamilyPowerOver f n ⟶ orderedFamilyPowerOver f m :=
  orderedFamilyTuple f (orderedFamilyPowerOver f n) m
    (fun i ↦ orderedFamilyCoordinate f n (ρ i))

/-- Reindexing has exactly the prescribed action on every coordinate. -/
theorem orderedFamilyReindex_coordinate {m n : ℕ} (ρ : Fin m → Fin n) (i : Fin m) :
    orderedFamilyReindex f ρ ≫ orderedFamilyCoordinate f m i =
      orderedFamilyCoordinate f n (ρ i) :=
  orderedFamilyTuple_coordinate f (orderedFamilyPowerOver f n) m _ i

/-- Identity reindexing is the identity morphism of the actual fiber power. -/
theorem orderedFamilyReindex_id (n : ℕ) :
    orderedFamilyReindex f (id : Fin n → Fin n) = 𝟙 (orderedFamilyPowerOver f n) := by
  apply orderedFamilyPower_coordinate_ext f _ n
  intro i
  rw [orderedFamilyReindex_coordinate, Category.id_comp]
  rfl

/-- Composition of reindexing agrees with composition of the coordinate maps. -/
theorem orderedFamilyReindex_comp {l m n : ℕ} (ρ : Fin m → Fin n) (τ : Fin l → Fin m) :
    orderedFamilyReindex f ρ ≫ orderedFamilyReindex f τ = orderedFamilyReindex f (ρ ∘ τ) := by
  apply orderedFamilyPower_coordinate_ext f _ l
  intro i
  rw [Category.assoc, orderedFamilyReindex_coordinate, orderedFamilyReindex_coordinate,
    orderedFamilyReindex_coordinate]
  rfl

/-- Every coordinate permutation induces an isomorphism over the original base. -/
noncomputable def orderedFamilyPermutationIso (n : ℕ) (e : Equiv.Perm (Fin n)) :
    orderedFamilyPowerOver f n ≅ orderedFamilyPowerOver f n where
  hom := orderedFamilyReindex f e
  inv := orderedFamilyReindex f e.symm
  hom_inv_id := by
    rw [orderedFamilyReindex_comp]
    convert orderedFamilyReindex_id f n using 1
    apply congrArg (orderedFamilyReindex f)
    funext i
    exact e.apply_symm_apply i
  inv_hom_id := by
    rw [orderedFamilyReindex_comp]
    convert orderedFamilyReindex_id f n using 1
    apply congrArg (orderedFamilyReindex f)
    funext i
    exact e.symm_apply_apply i

end AllCharacteristics
