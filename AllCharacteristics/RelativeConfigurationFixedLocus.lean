import AllCharacteristics.RelativeConfigurationFreeAction

/-!
# Empty fixed loci for nontrivial configuration permutations

Freeness on field-valued configurations implies scheme-theoretic freeness:
the equalizer of two different permutation maps has no points. Applying the
field-valued result to the residue field of a hypothetical equalizer point
retains its exact base morphism and works in every characteristic.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]

/-- The identity permutation acts by the identity on the actual configuration scheme. -/
theorem orderedFamilyConfigurationPermutationIso_refl_hom (n : ℕ) :
    (orderedFamilyConfigurationPermutationIso f n (Equiv.refl (Fin n))).hom =
      𝟙 (orderedFamilyConfigurationOver f n) := by
  exact orderedFamilyConfigurationReindex_id f n

/-- Two different permutation maps have an empty scheme-theoretic equalizer. -/
theorem isEmpty_configurationPermutation_equalizer (n : ℕ)
    (e e' : Equiv.Perm (Fin n)) (hne : e ≠ e') :
    IsEmpty (equalizer (orderedFamilyConfigurationPermutationIso f n e).hom
      (orderedFamilyConfigurationPermutationIso f n e').hom).left := by
  constructor
  intro x
  let E := equalizer (orderedFamilyConfigurationPermutationIso f n e).hom
    (orderedFamilyConfigurationPermutationIso f n e').hom
  let K : Type u := E.left.residueField x
  let r : Spec (.of K) ⟶ E.left := E.left.fromSpecResidueField x
  let b : Spec (.of K) ⟶ S := r ≫ E.hom
  let a : Over.mk b ⟶ E := Over.homMk r rfl
  let i := equalizer.ι (orderedFamilyConfigurationPermutationIso f n e).hom
    (orderedFamilyConfigurationPermutationIso f n e').hom
  apply hne
  apply fieldConfiguration_permutations_injective f n b (a ≫ i)
  have h := congrArg (fun z ↦ a ≫ z)
    (equalizer.condition (orderedFamilyConfigurationPermutationIso f n e).hom
      (orderedFamilyConfigurationPermutationIso f n e').hom)
  simpa only [Category.assoc] using h

/-- Every nonidentity permutation has empty fixed-point scheme on distinct configurations. -/
theorem isEmpty_configurationPermutation_fixedLocus (n : ℕ)
    (e : Equiv.Perm (Fin n)) (hne : e ≠ Equiv.refl (Fin n)) :
    IsEmpty (equalizer (orderedFamilyConfigurationPermutationIso f n e).hom
      (𝟙 (orderedFamilyConfigurationOver f n))).left := by
  simpa only [orderedFamilyConfigurationPermutationIso_refl_hom] using
    isEmpty_configurationPermutation_equalizer f n e (Equiv.refl (Fin n)) hne

end AllCharacteristics
