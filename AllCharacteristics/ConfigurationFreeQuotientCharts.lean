import AllCharacteristics.AffineSchemeFreeAction
import AllCharacteristics.RelativePermutationActions

/-! # Étale quotient maps for actual equivariant affine configuration charts -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (n : ℕ)

/-- No nonidentity permutation fixes an actual field-valued configuration,
regarded as a morphism of schemes. -/
theorem configurationRightAction_no_fixed_field_point
    (K : Type u) [Field K] (a : Spec (.of K) ⟶ (orderedFamilyConfigurationOver f n).left)
    (e : Equiv.Perm (Fin n)) (he : e ≠ 1) :
    a ≫ configurationRightAction f n e ≠ a := by
  intro ha
  let b : Spec (.of K) ⟶ S := a ≫ (orderedFamilyConfigurationOver f n).hom
  let p : Over.mk b ⟶ orderedFamilyConfigurationOver f n := Over.homMk a rfl
  apply he
  apply fieldConfiguration_permutations_injective f n b p
  apply Over.OverMorphism.ext
  change a ≫ configurationRightAction f n e = a ≫ configurationRightAction f n 1
  rw [configurationRightAction_one, Category.comp_id]
  exact ha

/-- Every actual equivariant affine chart mapping into the configuration
scheme has an étale invariant quotient. -/
theorem etale_affineConfigurationActionQuotientMap
    {Y : Scheme.{u}} [IsAffine Y]
    (ρ : Equiv.Perm (Fin n) → (Y ⟶ Y)) (h₁ : ρ 1 = 𝟙 Y)
    (hcomp : ∀ g h, ρ (g * h) = ρ g ≫ ρ h)
    (p : Y ⟶ S) (hp : ∀ g, ρ g ≫ p = p)
    (c : Y ⟶ (orderedFamilyConfigurationOver f n).left)
    (hc : ∀ g, ρ g ≫ c = c ≫ configurationRightAction f n g) :
    Etale (affineSchemeActionQuotientMap (Equiv.Perm (Fin n)) ρ h₁ hcomp p hp) := by
  apply etale_affineSchemeActionQuotientMap_of_free (Equiv.Perm (Fin n)) ρ h₁ hcomp p hp
  intro K _ a e he ha
  apply configurationRightAction_no_fixed_field_point f n K (a ≫ c) e he
  rw [Category.assoc, ← hc, ← Category.assoc, ha]

end AllCharacteristics
