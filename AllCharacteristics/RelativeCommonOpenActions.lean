import AllCharacteristics.RelativeOrderedMapGeometry
import AllCharacteristics.RelativePermutationActions
import AllCharacteristics.EquivariantOpenImage

/-!
# Stable affine common-open charts of ordered powers

A common open of the original family gives a permutation-stable open of each
ordered power. An affine common open over an affine base gives an affine
chart. Its function ring carries the constructed symmetric-group action,
fixing the actual coefficient functions from the base.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (n : ℕ)

/-- The common-open chart embedding is equivariant for the actual permutation morphisms. -/
theorem orderedFamilyCommonOpenPowerMap_equivariant (e : Equiv.Perm (Fin n)) :
    orderedFamilyRightAction (U.ι ≫ f) n e ≫
      Over.Hom.left (orderedFamilyCommonOpenPowerMap f U n) =
        Over.Hom.left (orderedFamilyCommonOpenPowerMap f U n) ≫ orderedFamilyRightAction f n e := by
  exact congrArg Over.Hom.left
    (orderedFamilyMap_reindex (U.ι ≫ f) f (Over.homMk U.ι rfl) e).symm

/-- The actual common-open chart is stable under every coordinate permutation. -/
theorem orderedFamilyCommonOpen_preimage (e : Equiv.Perm (Fin n)) :
    (orderedFamilyRightAction f n e) ⁻¹ᵁ orderedFamilyCommonOpen f U n =
      orderedFamilyCommonOpen f U n :=
  equivariant_opensRange_preimage (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (orderedFamilyRightAction_one f n) (orderedFamilyRightAction_mul f n)
    (orderedFamilyRightAction (U.ι ≫ f) n)
    (Over.Hom.left (orderedFamilyCommonOpenPowerMap f U n))
    (orderedFamilyCommonOpenPowerMap_equivariant f U n) e

/-- An affine common open over an affine base gives an actual affine open of the ordered power. -/
theorem isAffineOpen_orderedFamilyCommonOpen [IsAffine S] (hU : IsAffineOpen U) :
    IsAffineOpen (orderedFamilyCommonOpen f U n) := by
  have : IsAffine U.toScheme := hU
  exact isAffineOpen_opensRange (Over.Hom.left (orderedFamilyCommonOpenPowerMap f U n))

/-- Pullback along the actual chart permutations constructs its function-ring action. -/
@[instance_reducible]
noncomputable def orderedFamilyCommonOpenRingAction :
    MulSemiringAction (Equiv.Perm (Fin n)) Γ((orderedFamilyCommonOpen f U n).toScheme, ⊤) :=
  schemeRestrictedGlobalSectionAction (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (orderedFamilyRightAction_one f n) (orderedFamilyRightAction_mul f n)
    (orderedFamilyCommonOpen f U n) (orderedFamilyCommonOpen_preimage f U n)

/-- The actual permutation action on chart functions fixes the original base coefficients. -/
theorem orderedFamilyCommonOpenRingAction_smulComm :
    letI := orderedFamilyCommonOpenRingAction f U n
    letI := ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom).appTop.hom.toAlgebra
    SMulCommClass (Equiv.Perm (Fin n)) Γ(S, ⊤)
      Γ((orderedFamilyCommonOpen f U n).toScheme, ⊤) :=
  schemeRestrictedGlobalSectionAction_smulComm (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (orderedFamilyRightAction_one f n) (orderedFamilyRightAction_mul f n)
    (orderedFamilyCommonOpen f U n) (orderedFamilyCommonOpen_preimage f U n)
    (orderedFamilyPowerOver f n).hom (orderedFamilyRightAction_toBase f n)

end AllCharacteristics
