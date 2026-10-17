import AllCharacteristics.RelativeCommonOpenQuotientFunctor
import AllCharacteristics.AffineSchemeQuotientOpenImmersion

/-!
# Open immersion geometry of the actual unordered-tuple charts

Inclusions of affine common opens induce open immersions of the actual
unordered-tuple quotient charts. The original ordered-chart inclusion is
exactly their base change along the finite-group quotient map.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine S]
variable {U V : X.Opens} (hUV : U ≤ V) (n : ℕ)
variable (hU : IsAffineOpen U) (hV : IsAffineOpen V)

include hU hV in
/-- The actual inclusion of affine unordered-tuple quotient charts is an open immersion. -/
theorem isOpenImmersion_commonOpenTupleQuotientInclusion :
    IsOpenImmersion (commonOpenTupleQuotientInclusion f hUV n) := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  have : IsAffine (orderedFamilyCommonOpen f V n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f V n hV
  exact isOpenImmersion_affineSchemeActionQuotientMorphism (Equiv.Perm (Fin n))
    (commonOpenRightAction f U n) (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    (commonOpenRightAction f V n) (commonOpenRightAction_one f V n) (commonOpenRightAction_mul f V n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)
    ((orderedFamilyCommonOpen f V n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f V n)
    ((orderedFamilyPowerOver f n).left.homOfLE (orderedFamilyCommonOpen_mono f n hUV))
    (commonOpenChartInclusion_equivariant f hUV n)

/-- The quotient-chart inclusion and its original ordered-chart inclusion form
an actual Cartesian square. -/
theorem isPullback_commonOpenTupleQuotientInclusion :
    IsPullback
      ((orderedFamilyPowerOver f n).left.homOfLE (orderedFamilyCommonOpen_mono f n hUV))
      (commonOpenTupleQuotientMap f U n hU) (commonOpenTupleQuotientMap f V n hV)
      (commonOpenTupleQuotientInclusion f hUV n) := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  have : IsAffine (orderedFamilyCommonOpen f V n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f V n hV
  exact isPullback_affineSchemeActionQuotientMorphism (Equiv.Perm (Fin n))
    (commonOpenRightAction f U n) (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    (commonOpenRightAction f V n) (commonOpenRightAction_one f V n) (commonOpenRightAction_mul f V n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)
    ((orderedFamilyCommonOpen f V n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f V n)
    ((orderedFamilyPowerOver f n).left.homOfLE (orderedFamilyCommonOpen_mono f n hUV))
    (commonOpenChartInclusion_equivariant f hUV n)

include hU in
/-- Pulling back the quotient-chart range recovers exactly the ordered-chart range. -/
theorem commonOpenTupleQuotientInclusion_preimage_range :
    (commonOpenTupleQuotientMap f V n hV) ⁻¹'
      Set.range (commonOpenTupleQuotientInclusion f hUV n) =
        Set.range ((orderedFamilyPowerOver f n).left.homOfLE
          (orderedFamilyCommonOpen_mono f n hUV)) := by
  have : IsAffine (orderedFamilyCommonOpen f U n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U n hU
  have : IsAffine (orderedFamilyCommonOpen f V n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f V n hV
  exact affineSchemeActionQuotientMorphism_preimage_range (Equiv.Perm (Fin n))
    (commonOpenRightAction f U n) (commonOpenRightAction_one f U n) (commonOpenRightAction_mul f U n)
    (commonOpenRightAction f V n) (commonOpenRightAction_one f V n) (commonOpenRightAction_mul f V n)
    ((orderedFamilyCommonOpen f U n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U n)
    ((orderedFamilyCommonOpen f V n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f V n)
    ((orderedFamilyPowerOver f n).left.homOfLE (orderedFamilyCommonOpen_mono f n hUV))
    (commonOpenChartInclusion_equivariant f hUV n)

/-- The actual quotient-chart functor has open immersion transition maps. -/
instance isOpenImmersion_commonOpenTupleQuotientFunctor_map
    {U V : X.affineOpens} (h : U ⟶ V) :
    IsOpenImmersion (Over.Hom.left ((commonOpenTupleQuotientFunctor f n).map h)) :=
  isOpenImmersion_commonOpenTupleQuotientInclusion f h.le n U.property V.property

end AllCharacteristics
