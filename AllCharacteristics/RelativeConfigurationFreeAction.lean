import AllCharacteristics.RelativeConfigurationPermutations

/-!
# Freeness of coordinate permutations on field-valued configurations

Distinctness of the coordinate morphisms makes the permutation orbit of every
field-valued configuration injective. Thus the actual permutation maps have
no stabilizer at any field-valued point, in any characteristic.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]

/-- Different coordinate permutations give different images of every
field-valued distinct configuration, over exactly the same field. -/
theorem fieldConfiguration_permutations_injective (n : ℕ)
    {k : Type u} [Field k] (b : Spec (.of k) ⟶ S)
    (a : Over.mk b ⟶ orderedFamilyConfigurationOver f n) :
    Function.Injective (fun e : Equiv.Perm (Fin n) ↦
      a ≫ (orderedFamilyConfigurationPermutationIso f n e).hom) := by
  have ha : Over.Hom.left (a ≫ orderedFamilyConfigurationι f n)
      (IsLocalRing.closedPoint k) ∈ orderedFamilyConfigurationOpen f n := by
    change (orderedFamilyConfigurationOpen f n).ι
      (Over.Hom.left a (IsLocalRing.closedPoint k)) ∈ orderedFamilyConfigurationOpen f n
    exact (Over.Hom.left a (IsLocalRing.closedPoint k)).2
  have hc := (fieldTuple_mem_configuration_iff f n b
    (a ≫ orderedFamilyConfigurationι f n)).mp ha
  intro e e' h
  change a ≫ orderedFamilyConfigurationReindex f e e.injective =
    a ≫ orderedFamilyConfigurationReindex f e' e'.injective at h
  have hp := congrArg (fun z ↦ z ≫ orderedFamilyConfigurationι f n) h
  rw [Category.assoc, orderedFamilyConfigurationReindex_toPower,
    Category.assoc, orderedFamilyConfigurationReindex_toPower] at hp
  apply Equiv.ext
  intro i
  by_contra hne
  apply hc (e i) (e' i) hne
  have hi := congrArg (fun z ↦ z ≫ orderedFamilyCoordinate f n i) hp
  simpa only [Category.assoc, orderedFamilyReindex_coordinate] using hi

end AllCharacteristics
