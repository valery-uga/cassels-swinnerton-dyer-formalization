import AllCharacteristics.RelativeConfigurationFixedLocus
import AllCharacteristics.SchemeRestrictedAction

/-!
# Actual permutation actions and their rings of functions

Coordinate reindexing gives right actions of the symmetric group on the
ordered relative power and on its distinct-configuration open. These induce
actual ring actions on every stable open, preserving the base functions.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The actual right permutation action on the underlying ordered-power scheme. -/
noncomputable def orderedFamilyRightAction (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (orderedFamilyPowerOver f n).left ⟶ (orderedFamilyPowerOver f n).left :=
  Over.Hom.left (orderedFamilyReindex f e)

/-- A right permutation sends the `i`-th coordinate to the coordinate indexed
by the image of `i`. -/
theorem orderedFamilyRightAction_coordinate (n : ℕ)
    (e : Equiv.Perm (Fin n)) (i : Fin n) :
    orderedFamilyRightAction f n e ≫
        (orderedFamilyCoordinate f n i).left =
      (orderedFamilyCoordinate f n (e i)).left := by
  exact congrArg Over.Hom.left (orderedFamilyReindex_coordinate f e i)

/-- The identity permutation induces the identity on the actual ordered-power scheme. -/
theorem orderedFamilyRightAction_one (n : ℕ) :
    orderedFamilyRightAction f n 1 = 𝟙 (orderedFamilyPowerOver f n).left := by
  change Over.Hom.left (orderedFamilyReindex f (id : Fin n → Fin n)) = _
  rw [orderedFamilyReindex_id]
  rfl

/-- Permutation multiplication gives right composition on the ordered-power scheme. -/
theorem orderedFamilyRightAction_mul (n : ℕ) (e e' : Equiv.Perm (Fin n)) :
    orderedFamilyRightAction f n (e * e') =
      orderedFamilyRightAction f n e ≫ orderedFamilyRightAction f n e' := by
  change Over.Hom.left (orderedFamilyReindex f (e * e')) =
    Over.Hom.left (orderedFamilyReindex f e ≫ orderedFamilyReindex f e')
  rw [orderedFamilyReindex_comp]
  rfl

/-- The permutation action retains the actual original base morphism. -/
theorem orderedFamilyRightAction_toBase (n : ℕ) (e : Equiv.Perm (Fin n)) :
    orderedFamilyRightAction f n e ≫ (orderedFamilyPowerOver f n).hom =
      (orderedFamilyPowerOver f n).hom :=
  Over.w (orderedFamilyReindex f e)

variable [IsSeparated f]

/-- The actual right permutation action on the underlying distinct-configuration scheme. -/
noncomputable def configurationRightAction (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (orderedFamilyConfigurationOver f n).left ⟶ (orderedFamilyConfigurationOver f n).left :=
  Over.Hom.left (orderedFamilyConfigurationPermutationIso f n e).hom

/-- The identity acts trivially on the actual distinct-configuration scheme. -/
theorem configurationRightAction_one (n : ℕ) :
    configurationRightAction f n 1 = 𝟙 (orderedFamilyConfigurationOver f n).left := by
  change Over.Hom.left (orderedFamilyConfigurationPermutationIso f n (Equiv.refl (Fin n))).hom = _
  rw [orderedFamilyConfigurationPermutationIso_refl_hom]
  rfl

/-- Distinct-configuration permutations obey the right action composition law. -/
theorem configurationRightAction_mul (n : ℕ) (e e' : Equiv.Perm (Fin n)) :
    configurationRightAction f n (e * e') =
      configurationRightAction f n e ≫ configurationRightAction f n e' := by
  change Over.Hom.left (orderedFamilyConfigurationReindex f (e * e') (e * e').injective) =
    Over.Hom.left (orderedFamilyConfigurationReindex f e e.injective ≫
      orderedFamilyConfigurationReindex f e' e'.injective)
  rw [orderedFamilyConfigurationReindex_comp]
  rfl

/-- Configuration permutations preserve the original base morphism. -/
theorem configurationRightAction_toBase (n : ℕ) (e : Equiv.Perm (Fin n)) :
    configurationRightAction f n e ≫ (orderedFamilyConfigurationOver f n).hom =
      (orderedFamilyConfigurationOver f n).hom :=
  Over.w (orderedFamilyConfigurationPermutationIso f n e).hom

end AllCharacteristics
