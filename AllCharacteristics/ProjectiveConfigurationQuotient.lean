import AllCharacteristics.ProjectiveTupleQuotientOrbits
import AllCharacteristics.SchemeOrbitQuotientOpens
import AllCharacteristics.ConfigurationOpenStability

/-!
# The actual unordered distinct-configuration quotient for projective schemes

The original distinct-configuration open descends to an actual open in the
constructed projective tuple quotient. Its quotient map is the actual base
change of the full quotient, and is finite and surjective. Smoothness and
etaleness are not assumed in this construction.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- The actual full projective quotient carries the quotient topology. -/
theorem isQuotientMap_projectiveOrderedTupleQuotientMap :
    Topology.IsQuotientMap (projectiveOrderedTupleQuotientMap 𝒜 f n) :=
  (projectiveOrderedTupleQuotientMap 𝒜 f n).isClosedMap.isQuotientMap
    (projectiveOrderedTupleQuotientMap 𝒜 f n).continuous
    (projectiveOrderedTupleQuotientMap 𝒜 f n).surjective

/-- The actual full projective quotient morphism is open. -/
theorem isOpenMap_projectiveOrderedTupleQuotientMap :
    IsOpenMap (projectiveOrderedTupleQuotientMap 𝒜 f n) :=
  isOpenMap_schemeOrbitQuotient (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (projectiveOrderedTupleQuotientMap 𝒜 f n) (isQuotientMap_projectiveOrderedTupleQuotientMap 𝒜 f n)
    (projectiveOrderedTupleQuotientMap_eq_iff_orbit 𝒜 f n)

/-- The actual open of unordered pairwise distinct projective tuples. -/
noncomputable def projectiveConfigurationQuotientOpen : (projectiveOrderedTupleQuotient 𝒜 f n).Opens :=
  schemeOrbitQuotientOpen (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (projectiveOrderedTupleQuotientMap 𝒜 f n) (isQuotientMap_projectiveOrderedTupleQuotientMap 𝒜 f n)
    (projectiveOrderedTupleQuotientMap_eq_iff_orbit 𝒜 f n) (orderedFamilyConfigurationOpen f n)

/-- Pulling back the unordered distinct-configuration open recovers exactly
the actual original ordered configuration open. -/
theorem projectiveConfigurationQuotientOpen_preimage :
    (projectiveOrderedTupleQuotientMap 𝒜 f n) ⁻¹ᵁ projectiveConfigurationQuotientOpen 𝒜 f n =
      orderedFamilyConfigurationOpen f n :=
  schemeOrbitQuotientOpen_preimage (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (projectiveOrderedTupleQuotientMap 𝒜 f n) (isQuotientMap_projectiveOrderedTupleQuotientMap 𝒜 f n)
    (projectiveOrderedTupleQuotientMap_eq_iff_orbit 𝒜 f n) (orderedFamilyConfigurationOpen f n)
    (orderedFamilyConfigurationOpen_preimage f n)

/-- The actual quotient morphism from the original ordered distinct-configuration scheme. -/
noncomputable def projectiveConfigurationQuotientMap :
    (orderedFamilyConfigurationOver f n).left ⟶ (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme :=
  schemeOrbitOpenQuotientMap (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (projectiveOrderedTupleQuotientMap 𝒜 f n) (isQuotientMap_projectiveOrderedTupleQuotientMap 𝒜 f n)
    (projectiveOrderedTupleQuotientMap_eq_iff_orbit 𝒜 f n) (orderedFamilyConfigurationOpen f n)

/-- The actual distinct-configuration quotient square is Cartesian. -/
theorem isPullback_projectiveConfigurationQuotientMap :
    IsPullback (orderedFamilyConfigurationOpen f n).ι (projectiveConfigurationQuotientMap 𝒜 f n)
      (projectiveOrderedTupleQuotientMap 𝒜 f n) (projectiveConfigurationQuotientOpen 𝒜 f n).ι :=
  isPullback_schemeOrbitOpenQuotientMap (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (projectiveOrderedTupleQuotientMap 𝒜 f n) (isQuotientMap_projectiveOrderedTupleQuotientMap 𝒜 f n)
    (projectiveOrderedTupleQuotientMap_eq_iff_orbit 𝒜 f n) (orderedFamilyConfigurationOpen f n)
    (orderedFamilyConfigurationOpen_preimage f n)

/-- Every actual unordered distinct configuration has an ordered point above it. -/
instance surjective_projectiveConfigurationQuotientMap :
    Surjective (projectiveConfigurationQuotientMap 𝒜 f n) :=
  surjective_schemeOrbitOpenQuotientMap (Equiv.Perm (Fin n)) (orderedFamilyRightAction f n)
    (projectiveOrderedTupleQuotientMap 𝒜 f n) (isQuotientMap_projectiveOrderedTupleQuotientMap 𝒜 f n)
    (projectiveOrderedTupleQuotientMap_eq_iff_orbit 𝒜 f n) (orderedFamilyConfigurationOpen f n)

/-- The actual distinct-configuration quotient is integral. -/
instance isIntegralHom_projectiveConfigurationQuotientMap :
    IsIntegralHom (projectiveConfigurationQuotientMap 𝒜 f n) :=
  MorphismProperty.of_isPullback (P := @IsIntegralHom.{u})
    (isPullback_projectiveConfigurationQuotientMap 𝒜 f n) inferInstance

/-- For a locally finite-type projective family, the actual distinct-configuration quotient is finite. -/
instance isFinite_projectiveConfigurationQuotientMap [LocallyOfFiniteType f] :
    IsFinite (projectiveConfigurationQuotientMap 𝒜 f n) :=
  MorphismProperty.of_isPullback (P := @IsFinite.{u})
    (isPullback_projectiveConfigurationQuotientMap 𝒜 f n) inferInstance

/-- For a locally finite-type projective family, the actual distinct-configuration quotient is proper. -/
instance isProper_projectiveConfigurationQuotientMap [LocallyOfFiniteType f] :
    IsProper (projectiveConfigurationQuotientMap 𝒜 f n) := by
  infer_instance

end AllCharacteristics
