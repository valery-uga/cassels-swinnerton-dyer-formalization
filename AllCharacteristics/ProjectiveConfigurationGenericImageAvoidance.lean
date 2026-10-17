import AllCharacteristics.ProjectiveConfigurationQuotientAction
import AllCharacteristics.ProjectiveConfigurationGenericSpecialization

/-!
# Generic avoidance after passing from ordered to unordered configurations

An ordered configuration condition may be projected to the actual quotient by
the symmetric group.  When its image misses one quotient point, properness of
the finite quotient makes that image closed, and the generic point of the
unordered configuration avoids it.  This is the descent step needed to use
closed bad loci formed on labelled points in the generic configuration space
used by Voisin's residual construction.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

universe u v

variable {A : Type u} [CommRing A] {σ : Type v}
  [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- A closed condition on labelled configurations has a closed image on the
actual unordered configuration quotient.  If one unordered configuration has
no labelled lift in the condition, its generic function-field point avoids
that image. -/
theorem genericFunctionField_closedPoint_avoids_projectiveConfigurationImage_of_orbitWitness
    [LocallyOfFiniteType f]
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    (Z : Set (orderedFamilyConfigurationOver f n).left)
    (hZ : IsClosed Z)
    (hgood : ∃ x : (orderedFamilyConfigurationOver f n).left,
      ∀ y : (orderedFamilyConfigurationOver f n).left,
        projectiveConfigurationQuotientMap 𝒜 f n y =
          projectiveConfigurationQuotientMap 𝒜 f n x → y ∉ Z) :
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
      (IsLocalRing.closedPoint
        (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap 𝒜 f n '' Z := by
  apply genericFunctionField_closedPoint_avoids_proper_closed
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme
    ((projectiveConfigurationQuotientMap 𝒜 f n).isClosedMap Z hZ)
  intro htop
  obtain ⟨x, hx⟩ := hgood
  have hmem : projectiveConfigurationQuotientMap 𝒜 f n x ∈
      projectiveConfigurationQuotientMap 𝒜 f n '' Z := by
    rw [htop]
    exact Set.mem_univ _
  obtain ⟨y, hy, hxy⟩ := hmem
  exact hx y hxy hy

/-- A permutation-stable condition on labelled configurations misses a full
quotient fibre as soon as it misses one labelled configuration.  This removes
the extra orbit-witness hypothesis when the condition is built from a
symmetric incidence construction. -/
theorem projectiveConfiguration_orbitWitness_of_mapsTo_of_exists
    (Z : Set (orderedFamilyConfigurationOver f n).left)
    (hstable : ∀ g : Equiv.Perm (Fin n),
      Set.MapsTo (configurationRightAction f n g) Z Z)
    (hgood : ∃ x : (orderedFamilyConfigurationOver f n).left, x ∉ Z) :
    ∃ x : (orderedFamilyConfigurationOver f n).left,
      ∀ y : (orderedFamilyConfigurationOver f n).left,
        projectiveConfigurationQuotientMap 𝒜 f n y =
          projectiveConfigurationQuotientMap 𝒜 f n x → y ∉ Z := by
  obtain ⟨x, hx⟩ := hgood
  refine ⟨x, ?_⟩
  intro y hxy hy
  obtain ⟨g, hg⟩ :=
    (projectiveConfigurationQuotientMap_eq_iff_orbit 𝒜 f n x y).mp hxy.symm
  have hback : configurationRightAction f n g.symm y = x := by
    rw [← hg]
    have hgg : g * g.symm = 1 := by
      ext i
      simp
    have h := congrArg (fun a : (orderedFamilyConfigurationOver f n).left ⟶
      (orderedFamilyConfigurationOver f n).left ↦ a x)
      (configurationRightAction_mul f n g g.symm)
    rw [hgg, configurationRightAction_one] at h
    change x = configurationRightAction f n g.symm
      (configurationRightAction f n g x) at h
    exact h.symm
  have hbad : configurationRightAction f n g.symm y ∈ Z := hstable g.symm hy
  rw [hback] at hbad
  exact hx hbad

/-- A closed permutation-stable labelled condition with one witness outside
it has proper closed image on the unordered configuration quotient.  The
generic unordered configuration therefore avoids that image. -/
theorem genericFunctionField_closedPoint_avoids_projectiveConfigurationImage_of_mapsTo_of_exists
    [LocallyOfFiniteType f]
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    (Z : Set (orderedFamilyConfigurationOver f n).left)
    (hZ : IsClosed Z)
    (hstable : ∀ g : Equiv.Perm (Fin n),
      Set.MapsTo (configurationRightAction f n g) Z Z)
    (hgood : ∃ x : (orderedFamilyConfigurationOver f n).left, x ∉ Z) :
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
      (IsLocalRing.closedPoint
        (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap 𝒜 f n '' Z := by
  apply genericFunctionField_closedPoint_avoids_projectiveConfigurationImage_of_orbitWitness
    𝒜 f n Z hZ
  exact projectiveConfiguration_orbitWitness_of_mapsTo_of_exists 𝒜 f n Z hstable hgood

/-- The generic unordered configuration avoids every member of an indexed
family of permutation-invariant closed conditions when each condition misses
one quotient fibre.  The index can be the Picard group: genericity avoids the
bad locus for each divisor class separately, so no countability premise is
needed at this generic-point stage. -/
theorem genericFunctionField_closedPoint_avoids_projectiveConfigurationImage_family_of_orbitWitness
    [LocallyOfFiniteType f]
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    {κ : Sort v} (Z : κ → Set (orderedFamilyConfigurationOver f n).left)
    (hZ : ∀ c, IsClosed (Z c))
    (hgood : ∀ c, ∃ x : (orderedFamilyConfigurationOver f n).left,
      ∀ y : (orderedFamilyConfigurationOver f n).left,
        projectiveConfigurationQuotientMap 𝒜 f n y =
          projectiveConfigurationQuotientMap 𝒜 f n x → y ∉ Z c) :
    ∀ c,
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
        (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField) ∉
        projectiveConfigurationQuotientMap 𝒜 f n '' Z c := by
  intro c
  exact genericFunctionField_closedPoint_avoids_projectiveConfigurationImage_of_orbitWitness
    𝒜 f n (Z c) (hZ c) (hgood c)

/-- The generic unordered configuration avoids every member of an
arbitrarily indexed family of permutation-invariant bad loci as soon as each
bad locus misses one labelled configuration.  This is the Picard-class form
of generic avoidance: no countability assumption on the family is needed,
because the conclusion is pointwise in the class. -/
theorem genericFunctionField_closedPoint_avoids_projectiveConfigurationImage_family_of_mapsTo_of_exists
    [LocallyOfFiniteType f]
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    {κ : Sort v} (Z : κ → Set (orderedFamilyConfigurationOver f n).left)
    (hZ : ∀ c, IsClosed (Z c))
    (hstable : ∀ c, ∀ g : Equiv.Perm (Fin n),
      Set.MapsTo (configurationRightAction f n g) (Z c) (Z c))
    (hgood : ∀ c, ∃ x : (orderedFamilyConfigurationOver f n).left,
      x ∉ Z c) :
    ∀ c,
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
        (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField) ∉
        projectiveConfigurationQuotientMap 𝒜 f n '' Z c := by
  intro c
  exact genericFunctionField_closedPoint_avoids_projectiveConfigurationImage_of_mapsTo_of_exists
    𝒜 f n (Z c) (hZ c) (hstable c) (hgood c)

end AllCharacteristics
