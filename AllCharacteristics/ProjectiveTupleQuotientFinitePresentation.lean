import AllCharacteristics.ProjectiveConfigurationFiniteEtale
import AllCharacteristics.AffineSchemeQuotientFinitePresentation

/-! # Finite presentation of the actual projective tuple and configuration quotients -/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
variable (f : Proj 𝒜 ⟶ S) [LocallyOfFiniteType f] (n : ℕ)

/-- The full original projective tuple quotient is locally of finite
presentation over the original noetherian base. -/
instance locallyOfFinitePresentation_projectiveOrderedTupleQuotientToBase :
    LocallyOfFinitePresentation (projectiveOrderedTupleQuotientToBase 𝒜 f n) := by
  let : IsZariskiLocalAtSource (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _
      instHasRingHomPropertyLocallyOfFinitePresentationFinitePresentation
  change LocallyOfFinitePresentation (commonOpenTupleQuotientGluedToBase f n)
  apply IsZariskiLocalAtSource.of_openCover (commonOpenTupleQuotientGluedCover f n)
  intro U
  change (Proj 𝒜).affineOpens at U
  change LocallyOfFinitePresentation
    (commonOpenTupleQuotientGluedChart f n U ≫ commonOpenTupleQuotientGluedToBase f n)
  rw [commonOpenTupleQuotientGluedChart_toBase]
  have : IsAffine (orderedFamilyCommonOpen f U.val n).toScheme :=
    isAffineOpen_orderedFamilyCommonOpen f U.val n U.property
  exact locallyOfFinitePresentation_affineSchemeActionQuotientToBase (Equiv.Perm (Fin n))
    (commonOpenRightAction f U.val n) (commonOpenRightAction_one f U.val n)
    (commonOpenRightAction_mul f U.val n)
    ((orderedFamilyCommonOpen f U.val n).ι ≫ (orderedFamilyPowerOver f n).hom)
    (commonOpenRightAction_toBase f U.val n)

/-- The actual unordered distinct-configuration parameter scheme is locally
of finite presentation over the original noetherian base. -/
instance locallyOfFinitePresentation_projectiveConfigurationQuotientToBase :
    LocallyOfFinitePresentation (projectiveConfigurationQuotientToBase 𝒜 f n) := by
  change LocallyOfFinitePresentation
    ((projectiveConfigurationQuotientOpen 𝒜 f n).ι ≫ projectiveOrderedTupleQuotientToBase 𝒜 f n)
  infer_instance

/-- The actual full projective tuple quotient is locally noetherian. -/
instance isLocallyNoetherian_projectiveOrderedTupleQuotient :
    IsLocallyNoetherian (projectiveOrderedTupleQuotient 𝒜 f n) :=
  LocallyOfFiniteType.isLocallyNoetherian (projectiveOrderedTupleQuotientToBase 𝒜 f n)

/-- The actual unordered configuration scheme is locally noetherian. -/
instance isLocallyNoetherian_projectiveConfigurationQuotient :
    IsLocallyNoetherian (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme :=
  LocallyOfFiniteType.isLocallyNoetherian (projectiveConfigurationQuotientToBase 𝒜 f n)

end AllCharacteristics
