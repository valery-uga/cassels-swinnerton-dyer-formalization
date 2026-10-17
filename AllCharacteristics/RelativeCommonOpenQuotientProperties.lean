import AllCharacteristics.RelativeCommonOpenQuotient

/-!
# Finiteness and properness of the unordered-tuple chart quotients

For finite-type families, the actual quotient morphisms of the stable affine
common-open charts are finite, surjective, and proper. The argument uses the
constructed permutation actions and finite-group invariant rings, without
any characteristic restriction or a presumed global symmetric-power scheme.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Every finite ordered power of a locally finite-type family is locally of finite type. -/
instance locallyOfFiniteType_orderedFamilyPower [LocallyOfFiniteType f] (n : ℕ) :
    LocallyOfFiniteType (orderedFamilyPowerOver f n).hom := by
  induction n with
  | zero =>
    change LocallyOfFiniteType (𝟙 S)
    infer_instance
  | succ n ih =>
    have := ih
    change LocallyOfFiniteType (pullback.fst f (orderedFamilyPowerOver f n).hom ≫ f)
    infer_instance

variable (U : X.Opens) (n : ℕ) [IsAffine S] (hU : IsAffineOpen U)

/-- The actual chart quotient map is integral. -/
instance isIntegralHom_commonOpenTupleQuotientMap :
    IsIntegralHom (commonOpenTupleQuotientMap f U n hU) := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  exact isIntegralHom_affineSchemeActionQuotientMap (Equiv.Perm (Fin n)) (commonOpenRightAction f U n)
    (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)

/-- The actual chart quotient map is surjective. -/
instance surjective_commonOpenTupleQuotientMap :
    Surjective (commonOpenTupleQuotientMap f U n hU) := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  exact surjective_affineSchemeActionQuotientMap (Equiv.Perm (Fin n)) (commonOpenRightAction f U n)
    (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)

/-- For a locally finite-type family the actual chart quotient map is finite. -/
instance isFinite_commonOpenTupleQuotientMap [LocallyOfFiniteType f] :
    IsFinite (commonOpenTupleQuotientMap f U n hU) := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  exact isFinite_affineSchemeActionQuotientMap (Equiv.Perm (Fin n)) (commonOpenRightAction f U n)
    (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)

/-- For a locally finite-type family the actual chart quotient map is proper. -/
instance isProper_commonOpenTupleQuotientMap [LocallyOfFiniteType f] :
    IsProper (commonOpenTupleQuotientMap f U n hU) := by
  infer_instance

end AllCharacteristics
