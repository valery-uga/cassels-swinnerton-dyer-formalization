import AllCharacteristics.AffineQuotientFreeOpenEtale
import AllCharacteristics.EquivariantOpenRestriction
import AllCharacteristics.ConfigurationFreeQuotientCharts
import AllCharacteristics.ConfigurationOpenStability
import AllCharacteristics.RelativeCommonOpenQuotient

/-! # Étaleness on the actual configuration part of each common-affine chart -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (U : X.Opens) (n : ℕ)

/-- Configuration permutations commute with the original inclusion in the ordered power. -/
theorem configurationRightAction_ι (g : Equiv.Perm (Fin n)) :
    configurationRightAction f n g ≫ (orderedFamilyConfigurationOpen f n).ι =
      (orderedFamilyConfigurationOpen f n).ι ≫ orderedFamilyRightAction f n g :=
  orderedFamilyConfigurationReindex_ι f g g.injective

/-- The actual configuration open in the common-open ordered tuple chart. -/
noncomputable def commonOpenConfiguration : (orderedFamilyCommonOpen f U n).toScheme.Opens :=
  (orderedFamilyCommonOpen f U n).ι ⁻¹ᵁ orderedFamilyConfigurationOpen f n

/-- The actual common-open chart inclusion restricts to the original configuration scheme. -/
noncomputable def commonOpenConfigurationToConfiguration :
    (commonOpenConfiguration f U n).toScheme ⟶ (orderedFamilyConfigurationOver f n).left :=
  (orderedFamilyCommonOpen f U n).ι ∣_ orderedFamilyConfigurationOpen f n

/-- This configuration chart morphism is an actual open immersion. -/
instance isOpenImmersion_commonOpenConfigurationToConfiguration :
    IsOpenImmersion (commonOpenConfigurationToConfiguration f U n) := by
  exact inferInstanceAs (IsOpenImmersion
    ((orderedFamilyCommonOpen f U n).ι ∣_ orderedFamilyConfigurationOpen f n))

/-- Common-open configurations are stable under the actual chart permutations. -/
theorem commonOpenConfiguration_preimage (g : Equiv.Perm (Fin n)) :
    (commonOpenRightAction f U n g) ⁻¹ᵁ commonOpenConfiguration f U n =
      commonOpenConfiguration f U n :=
  equivariant_preimage_open_stable (Equiv.Perm (Fin n)) (commonOpenRightAction f U n)
    (orderedFamilyRightAction f n) (orderedFamilyCommonOpen f U n).ι
    (schemeRestrictedRightAction_ι (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
      (orderedFamilyCommonOpen f U n) (orderedFamilyCommonOpen_preimage f U n))
    (orderedFamilyConfigurationOpen f n) (orderedFamilyConfigurationOpen_preimage f n) g

/-- The restricted common-open action agrees with the actual configuration action. -/
theorem commonOpenConfigurationToConfiguration_equivariant (g : Equiv.Perm (Fin n)) :
    schemeRestrictedRightAction (Equiv.Perm (Fin n)) (commonOpenRightAction f U n)
      (commonOpenConfiguration f U n) (commonOpenConfiguration_preimage f U n) g ≫
        commonOpenConfigurationToConfiguration f U n =
      commonOpenConfigurationToConfiguration f U n ≫ configurationRightAction f n g :=
  equivariant_morphismRestrict (Equiv.Perm (Fin n)) (commonOpenRightAction f U n)
    (orderedFamilyRightAction f n) (orderedFamilyCommonOpen f U n).ι
    (schemeRestrictedRightAction_ι (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
      (orderedFamilyCommonOpen f U n) (orderedFamilyCommonOpen_preimage f U n))
    (orderedFamilyConfigurationOpen f n) (orderedFamilyConfigurationOpen_preimage f n)
    (configurationRightAction f n) (configurationRightAction_ι f n) g

/-- The original affine quotient map is étale on its actual distinct-configuration open. -/
theorem etale_commonOpenTupleQuotientMap_on_configuration [IsAffine S] (hU : IsAffineOpen U) :
    Etale ((commonOpenConfiguration f U n).ι ≫ commonOpenTupleQuotientMap f U n hU) := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  apply etale_affineSchemeActionQuotientMap_on_free_open (Equiv.Perm (Fin n))
    (commonOpenRightAction f U n) (commonOpenRightAction_one f U n)
    (commonOpenRightAction_mul f U n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n) (commonOpenConfiguration f U n)
    (commonOpenConfiguration_preimage f U n)
  intro K _ a g hg ha
  apply configurationRightAction_no_fixed_field_point f n K
    (a ≫ commonOpenConfigurationToConfiguration f U n) g hg
  rw [Category.assoc, ← commonOpenConfigurationToConfiguration_equivariant,
    ← Category.assoc, ha]

end AllCharacteristics
