import AllCharacteristics.ProjectiveConfigurationGenericImageAvoidance

/-!
# Proper finite incidence for arbitrary section systems

Voisin's fixed-divisor argument uses projective spaces of sections of line
bundles, rather than only homogeneous polynomial systems.  This file isolates
the common topological mechanism.  A proper parameter family `T`, a closed
incidence relation in any target `Y`, and one incidence map for each marked
point determine a closed bad locus on the configuration base.  The generic
point of an integral configuration base avoids that locus as soon as one good
configuration exists.

The construction is independent of a presentation of the sections.  It is
therefore the interface needed for the Picard-class-indexed systems in the
last step of Voisin's degree-eight fixed-component argument.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics

universe u

/-- Adjoin a proper parameter family to a configuration base over the same
coefficient scheme. -/
noncomputable abbrev properFiniteIncidenceParameterSpace
    {S X T : Scheme.{u}} (xBase : X ⟶ S) (tBase : T ⟶ S) : Scheme.{u} :=
  pullback xBase tBase

/-- The locus of configurations for which one parameter satisfies every
marked closed incidence condition. -/
noncomputable def properFiniteIncidenceBadLocus
    {S X T Y : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ S) (tBase : T ⟶ S)
    (incidenceMap : ι → (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (incidence : Set Y) : Set X :=
  pullback.fst xBase tBase ''
    ⋂ i, (incidenceMap i) ⁻¹' incidence

/-- Membership in the bad locus is exactly a common parameter over the
configuration satisfying every marked incidence condition. -/
theorem exists_parameter_of_mem_properFiniteIncidenceBadLocus
    {S X T Y : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ S) (tBase : T ⟶ S)
    (incidenceMap : ι → (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (incidence : Set Y) {x : X}
    (hx : x ∈ properFiniteIncidenceBadLocus
      xBase tBase incidenceMap incidence) :
    ∃ z : properFiniteIncidenceParameterSpace xBase tBase,
      pullback.fst xBase tBase z = x ∧
        ∀ i, incidenceMap i z ∈ incidence := by
  obtain ⟨z, hz, hzx⟩ := hx
  refine ⟨z, hzx, ?_⟩
  intro i
  exact Set.mem_iInter.mp hz i

/-- A common parameter satisfying all marked conditions gives membership in
the bad locus. -/
theorem mem_properFiniteIncidenceBadLocus_of_parameter
    {S X T Y : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ S) (tBase : T ⟶ S)
    (incidenceMap : ι → (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (incidence : Set Y)
    (z : properFiniteIncidenceParameterSpace xBase tBase)
    (hz : ∀ i, incidenceMap i z ∈ incidence) :
    pullback.fst xBase tBase z ∈
      properFiniteIncidenceBadLocus xBase tBase incidenceMap incidence := by
  refine ⟨z, ?_, rfl⟩
  exact Set.mem_iInter.mpr hz

/-- Properness of the parameter family makes the simultaneous closed
incidence locus closed on the configuration base. -/
theorem isClosed_properFiniteIncidenceBadLocus
    {S X T Y : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (incidenceMap : ι → (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (incidence : Set Y) (hincidence : IsClosed incidence) :
    IsClosed (properFiniteIncidenceBadLocus
      xBase tBase incidenceMap incidence) := by
  let π : properFiniteIncidenceParameterSpace xBase tBase ⟶ X :=
    pullback.fst xBase tBase
  letI : IsProper π := by
    dsimp only [π, properFiniteIncidenceParameterSpace]
    infer_instance
  change IsClosed (π '' ⋂ i, (incidenceMap i) ⁻¹' incidence)
  apply π.isClosedMap
  apply isClosed_iInter
  intro i
  exact hincidence.preimage (incidenceMap i).continuous

/-- A closed-immersion zero family supplies the closed incidence relation
required by the abstract construction. -/
theorem isClosed_properFiniteIncidenceBadLocus_of_closedImmersion
    {S X T Y Z : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (incidenceMap : ι → (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (zeroFamily : Z ⟶ Y) [IsClosedImmersion zeroFamily] :
    IsClosed (properFiniteIncidenceBadLocus
      xBase tBase incidenceMap (Set.range zeroFamily)) := by
  exact isClosed_properFiniteIncidenceBadLocus
    xBase tBase incidenceMap (Set.range zeroFamily)
      zeroFamily.isClosedEmbedding.isClosed_range

/-- The generic point of an integral configuration base avoids every proper
bad locus arising from a proper finite-incidence system. -/
theorem genericFunctionField_closedPoint_avoids_properFiniteIncidence
    {S X T Y : Scheme.{u}} {ι : Type} [IsIntegral X]
    (xBase : X ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (incidenceMap : ι → (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (incidence : Set Y) (hincidence : IsClosed incidence)
    (hproper : properFiniteIncidenceBadLocus
      xBase tBase incidenceMap incidence ≠ Set.univ) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      properFiniteIncidenceBadLocus xBase tBase incidenceMap incidence := by
  exact genericFunctionField_closedPoint_avoids_proper_closed X
    (isClosed_properFiniteIncidenceBadLocus
      xBase tBase incidenceMap incidence hincidence) hproper

/-- One good configuration proves the bad locus proper and hence gives
generic avoidance. -/
theorem genericFunctionField_closedPoint_avoids_properFiniteIncidence_of_exists
    {S X T Y : Scheme.{u}} {ι : Type} [IsIntegral X]
    (xBase : X ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (incidenceMap : ι → (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (incidence : Set Y) (hincidence : IsClosed incidence)
    (hgood : ∃ x : X,
      x ∉ properFiniteIncidenceBadLocus xBase tBase incidenceMap incidence) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      properFiniteIncidenceBadLocus xBase tBase incidenceMap incidence := by
  apply genericFunctionField_closedPoint_avoids_properFiniteIncidence
    xBase tBase incidenceMap incidence hincidence
  intro hbad
  obtain ⟨x, hx⟩ := hgood
  apply hx
  rw [hbad]
  exact Set.mem_univ x

/-- Closed-immersion form of generic avoidance, ready for a universal zero
scheme of a projective family of line-bundle sections. -/
theorem
    genericFunctionField_closedPoint_avoids_properFiniteIncidenceRange_of_exists
    {S X T Y Z : Scheme.{u}} {ι : Type} [IsIntegral X]
    (xBase : X ⟶ S) (tBase : T ⟶ S) [IsProper tBase]
    (incidenceMap : ι → (properFiniteIncidenceParameterSpace xBase tBase ⟶ Y))
    (zeroFamily : Z ⟶ Y) [IsClosedImmersion zeroFamily]
    (hgood : ∃ x : X,
      x ∉ properFiniteIncidenceBadLocus
        xBase tBase incidenceMap (Set.range zeroFamily)) :
    X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField) ∉
      properFiniteIncidenceBadLocus
        xBase tBase incidenceMap (Set.range zeroFamily) := by
  exact genericFunctionField_closedPoint_avoids_properFiniteIncidence_of_exists
    xBase tBase incidenceMap (Set.range zeroFamily)
      zeroFamily.isClosedEmbedding.isClosed_range hgood

end PfaffianDescent
