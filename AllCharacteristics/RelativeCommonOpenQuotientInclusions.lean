import AllCharacteristics.RelativeCommonOpenQuotientProperties
import AllCharacteristics.RelativeCommonOpenIntersections
import AllCharacteristics.AffineSchemeActionQuotientMorphism
import AllCharacteristics.SchemeRestrictedActionInclusions

/-!
# Actual maps between the unordered-tuple quotient charts

Inclusions of common opens give equivariant inclusions of the actual tuple
charts and hence constructed morphisms of their invariant quotients. The
quotient squares commute with the original chart inclusions and retain the
actual structure morphism to the original base.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) {U V : X.Opens} (hUV : U ≤ V) (n : ℕ)

/-- Inclusion of actual common-open charts is equivariant for their permutation actions. -/
theorem commonOpenChartInclusion_equivariant (e : Equiv.Perm (Fin n)) :
    commonOpenRightAction f U n e ≫
      (orderedFamilyPowerOver f n).left.homOfLE (orderedFamilyCommonOpen_mono f n hUV) =
        (orderedFamilyPowerOver f n).left.homOfLE (orderedFamilyCommonOpen_mono f n hUV) ≫
          commonOpenRightAction f V n e :=
  schemeRestrictedRightAction_homOfLE (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (orderedFamilyCommonOpen f U n) (orderedFamilyCommonOpen f V n)
    (orderedFamilyCommonOpen_preimage f U n) (orderedFamilyCommonOpen_preimage f V n)
    (orderedFamilyCommonOpen_mono f n hUV) e

/-- The actual invariant-quotient morphism induced by inclusion of common-open tuple charts. -/
noncomputable def commonOpenTupleQuotientInclusion :
    commonOpenTupleQuotient f U n ⟶ commonOpenTupleQuotient f V n :=
  affineSchemeActionQuotientMorphism (Equiv.Perm (Fin n))
    (commonOpenRightAction f U n) (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    (commonOpenRightAction f V n) (commonOpenRightAction_one f V n) (commonOpenRightAction_mul f V n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)
    ((orderedFamilyCommonOpen f V n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f V n)
    ((orderedFamilyPowerOver f n).left.homOfLE (orderedFamilyCommonOpen_mono f n hUV))
    (commonOpenChartInclusion_equivariant f hUV n)

variable [IsAffine S] (hU : IsAffineOpen U) (hV : IsAffineOpen V)

/-- The quotient-chart inclusion square commutes with the original actual chart maps. -/
theorem commonOpenTupleQuotientInclusion_square :
    commonOpenTupleQuotientMap f U n hU ≫ commonOpenTupleQuotientInclusion f hUV n =
      (orderedFamilyPowerOver f n).left.homOfLE (orderedFamilyCommonOpen_mono f n hUV) ≫
        commonOpenTupleQuotientMap f V n hV := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  have : IsAffine (orderedFamilyCommonOpen f V n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f V n hV
  exact affineSchemeActionQuotientMorphism_square (Equiv.Perm (Fin n))
    (commonOpenRightAction f U n) (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    (commonOpenRightAction f V n) (commonOpenRightAction_one f V n) (commonOpenRightAction_mul f V n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)
    ((orderedFamilyCommonOpen f V n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f V n)
    ((orderedFamilyPowerOver f n).left.homOfLE (orderedFamilyCommonOpen_mono f n hUV))
    (commonOpenChartInclusion_equivariant f hUV n)

include hU hV in
/-- The actual quotient-chart inclusion retains the original affine base morphism. -/
theorem commonOpenTupleQuotientInclusion_toBase :
    commonOpenTupleQuotientInclusion f hUV n ≫ commonOpenTupleQuotientToBase f V n =
      commonOpenTupleQuotientToBase f U n := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  have : IsAffine (orderedFamilyCommonOpen f V n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f V n hV
  apply affineSchemeActionQuotientMorphism_toBase (Equiv.Perm (Fin n))
    (commonOpenRightAction f U n) (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    (commonOpenRightAction f V n) (commonOpenRightAction_one f V n) (commonOpenRightAction_mul f V n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)
    ((orderedFamilyCommonOpen f V n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f V n)
    ((orderedFamilyPowerOver f n).left.homOfLE (orderedFamilyCommonOpen_mono f n hUV))
    (commonOpenChartInclusion_equivariant f hUV n)
  rw [← Category.assoc, Scheme.homOfLE_ι]

end AllCharacteristics
