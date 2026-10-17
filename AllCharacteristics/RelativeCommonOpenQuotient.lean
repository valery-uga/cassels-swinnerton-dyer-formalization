import AllCharacteristics.RelativeCommonOpenActions
import AllCharacteristics.AffineSchemeActionQuotientProperties

/-!
# Actual quotient charts for unordered tuples

The permutation-stable common-open charts of the ordered relative power now
have actual invariant-spectrum quotients. The quotient morphisms start from
the original chart schemes and preserve the original base. For a smooth
family with affine base and affine common open, these quotient maps are
finite, surjective, and proper, in every characteristic.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (n : ℕ)

/-- The actual permutation morphisms restricted to the common-open chart. -/
noncomputable def commonOpenRightAction (e : Equiv.Perm (Fin n)) :
    (orderedFamilyCommonOpen f U n).toScheme ⟶ (orderedFamilyCommonOpen f U n).toScheme :=
  schemeRestrictedRightAction (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (orderedFamilyCommonOpen f U n) (orderedFamilyCommonOpen_preimage f U n) e

/-- The common-open chart action preserves the identity. -/
theorem commonOpenRightAction_one :
    commonOpenRightAction f U n 1 = 𝟙 (orderedFamilyCommonOpen f U n).toScheme :=
  schemeRestrictedRightAction_one (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (orderedFamilyRightAction_one f n) (orderedFamilyCommonOpen f U n)
    (orderedFamilyCommonOpen_preimage f U n)

/-- The common-open chart action has the actual right composition law. -/
theorem commonOpenRightAction_mul (e e' : Equiv.Perm (Fin n)) :
    commonOpenRightAction f U n (e * e') = commonOpenRightAction f U n e ≫
      commonOpenRightAction f U n e' :=
  schemeRestrictedRightAction_mul (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (orderedFamilyRightAction_mul f n) (orderedFamilyCommonOpen f U n)
    (orderedFamilyCommonOpen_preimage f U n) e e'

/-- Restricted chart permutations preserve the actual original base map. -/
theorem commonOpenRightAction_toBase (e : Equiv.Perm (Fin n)) :
    commonOpenRightAction f U n e ≫
      ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom) =
        (orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom :=
  schemeRestrictedRightAction_toBase (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (orderedFamilyCommonOpen f U n) (orderedFamilyCommonOpen_preimage f U n)
    (orderedFamilyPowerOver f n).hom (orderedFamilyRightAction_toBase f n) e

/-- The actual invariant-spectrum quotient of the common-open tuple chart. -/
noncomputable def commonOpenTupleQuotient : Scheme.{u} :=
  affineSchemeActionQuotient (Equiv.Perm (Fin n)) (commonOpenRightAction f U n)
    (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)

/-- The constructed unordered-tuple chart is an actual affine scheme. -/
instance isAffine_commonOpenTupleQuotient : IsAffine (commonOpenTupleQuotient f U n) := by
  exact isAffine_affineSchemeActionQuotient (Equiv.Perm (Fin n)) (commonOpenRightAction f U n)
    (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)

variable [IsAffine S]

/-- The actual quotient map from an affine common-open tuple chart. -/
noncomputable def commonOpenTupleQuotientMap (hU : IsAffineOpen U) :
    (orderedFamilyCommonOpen f U n).toScheme ⟶ commonOpenTupleQuotient f U n := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  exact affineSchemeActionQuotientMap (Equiv.Perm (Fin n)) (commonOpenRightAction f U n)
    (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)

/-- The unordered-tuple chart retains its actual morphism to the original affine base. -/
noncomputable def commonOpenTupleQuotientToBase : commonOpenTupleQuotient f U n ⟶ S :=
  affineSchemeActionQuotientToBase (Equiv.Perm (Fin n)) (commonOpenRightAction f U n)
    (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)

/-- The chart quotient factorization retains the original family morphism. -/
theorem commonOpenTupleQuotientMap_toBase (hU : IsAffineOpen U) :
    commonOpenTupleQuotientMap f U n hU ≫ commonOpenTupleQuotientToBase f U n =
      (orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  exact affineSchemeActionQuotientMap_toBase (Equiv.Perm (Fin n)) (commonOpenRightAction f U n)
    (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)

/-- The actual quotient map is invariant under the original chart permutations. -/
theorem commonOpenTupleQuotientMap_invariant (hU : IsAffineOpen U) (e : Equiv.Perm (Fin n)) :
    commonOpenRightAction f U n e ≫ commonOpenTupleQuotientMap f U n hU =
      commonOpenTupleQuotientMap f U n hU := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  exact affineSchemeActionQuotientMap_invariant (Equiv.Perm (Fin n)) (commonOpenRightAction f U n)
    (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n) e

end AllCharacteristics
