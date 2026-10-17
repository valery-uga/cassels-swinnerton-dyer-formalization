import PfaffianDescent.VoisinFixedLinearSystemDescentEndpoint
import AllCharacteristics.OrderedConfigurationSections
import AllCharacteristics.OrderedConfigurationMarkedAction
import AllCharacteristics.ProjectiveConfigurationGenericImageAvoidance

/-!
# Fixed linear systems on the unordered configuration quotient

The universal zero family of a fixed line bundle is naturally constructed on
the ordered configuration space, where the marked points are honest
morphisms.  Voisin's generic finite subscheme, however, is the generic point
of the quotient by the symmetric group.  This file proves that the
simultaneous-zero bad locus is permutation invariant and therefore has a
proper closed image on that quotient as soon as one labelled configuration
avoids it.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics

universe u v

/-- Reindexing the marked maps preserves the locus on which one common
parameter makes all of them land in a fixed closed incidence family. -/
theorem mapsTo_fixedLinearSystemBadLocus_of_reindex
    {S X W T Z : Scheme.{u}} {ι : Type}
    (xBase : X ⟶ S) (wBase : W ⟶ S) (tBase : T ⟶ S)
    (marked : ι → (X ⟶ W))
    (hmarked : ∀ i, marked i ≫ wBase = xBase)
    (zeroFamily : Z ⟶ pullback wBase tBase)
    (action : X ⟶ X) (haction : action ≫ xBase = xBase)
    (g : ι ≃ ι) (haction_marked : ∀ i, action ≫ marked i = marked (g i)) :
    Set.MapsTo action
      (fixedLinearSystemBadLocus
        xBase wBase tBase (marked := marked) hmarked zeroFamily)
      (fixedLinearSystemBadLocus
        xBase wBase tBase (marked := marked) hmarked zeroFamily) := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hx
  let actionParam : properFiniteIncidenceParameterSpace xBase tBase ⟶
      properFiniteIncidenceParameterSpace xBase tBase :=
    pullback.lift
      (pullback.fst xBase tBase ≫ action)
      (pullback.snd xBase tBase) (by
        rw [Category.assoc, haction]
        exact pullback.condition)
  refine ⟨actionParam z, ?_, ?_⟩
  · apply Set.mem_iInter.mpr
    intro i
    have hi := Set.mem_iInter.mp hz (g i)
    obtain ⟨y, hy⟩ := hi
    refine ⟨y, ?_⟩
    have hmap : actionParam ≫
          fixedLinearSystemIncidenceMap
            xBase wBase tBase marked hmarked i =
        fixedLinearSystemIncidenceMap
          xBase wBase tBase marked hmarked (g i) := by
      apply pullback.hom_ext
      · rw [Category.assoc, fixedLinearSystemIncidenceMap_fst,
          fixedLinearSystemIncidenceMap_fst]
        dsimp only [actionParam]
        rw [pullback.lift_fst_assoc]
        rw [Category.assoc, haction_marked]
      · rw [Category.assoc, fixedLinearSystemIncidenceMap_snd,
          fixedLinearSystemIncidenceMap_snd]
        exact pullback.lift_snd _ _ _
    have hpoint := congrArg (fun k => k z) hmap
    exact hy.trans hpoint.symm
  · have hfstMap : actionParam ≫ pullback.fst xBase tBase =
        pullback.fst xBase tBase ≫ action := by
      dsimp only [actionParam]
      exact pullback.lift_fst _ _ _
    have hfst := congrArg (fun k => k z) hfstMap
    change pullback.fst xBase tBase (actionParam z) = action x
    rw [← hzx]
    simpa only [Scheme.Hom.comp_apply] using hfst

section OrderedConfigurations

variable {A : Type u} [CommRing A] {σ : Type v}
  [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S]
  (f : Proj 𝒜 ⟶ S) [IsSeparated f] (n : ℕ)

/-- The `i`th point of an ordered configuration, retained as a point of the
original projective family rather than mapped to an ambient projective
space. -/
noncomputable def orderedConfigurationSurfacePoint (i : Fin n) :
    (orderedFamilyConfigurationOver f n).left ⟶ Proj 𝒜 :=
  (orderedFamilyConfigurationOpen f n).ι ≫
    (orderedFamilyCoordinate f n i).left

@[reassoc]
theorem orderedConfigurationSurfacePoint_toBase (i : Fin n) :
    orderedConfigurationSurfacePoint 𝒜 f n i ≫ f =
      (orderedFamilyConfigurationOver f n).hom := by
  unfold orderedConfigurationSurfacePoint
  change (((orderedFamilyConfigurationOpen f n).ι ≫
      (orderedFamilyCoordinate f n i).left) ≫ f) =
    (orderedFamilyConfigurationOpen f n).ι ≫
      (orderedFamilyPowerOver f n).hom
  have hw := (orderedFamilyCoordinate f n i).w
  change (orderedFamilyCoordinate f n i).left ≫ f =
    (orderedFamilyPowerOver f n).hom at hw
  rw [Category.assoc, hw]

@[reassoc]
theorem configurationRightAction_orderedConfigurationSurfacePoint
    (g : Equiv.Perm (Fin n)) (i : Fin n) :
    configurationRightAction f n g ≫
        orderedConfigurationSurfacePoint 𝒜 f n i =
      orderedConfigurationSurfacePoint 𝒜 f n (g i) := by
  unfold orderedConfigurationSurfacePoint
  change configurationRightAction f n g ≫
      (orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n i).left =
    (orderedFamilyConfigurationOpen f n).ι ≫
      (orderedFamilyCoordinate f n (g i)).left
  exact configurationRightAction_coordinate f n g i

/-- The simultaneous zero locus of a fixed line-bundle section system is
stable under every permutation of an ordered configuration. -/
theorem mapsTo_orderedConfiguration_fixedLinearSystemBadLocus
    {T Z : Scheme.{u}} (tBase : T ⟶ S)
    (zeroFamily : Z ⟶ pullback f tBase)
    (g : Equiv.Perm (Fin n)) :
    Set.MapsTo (configurationRightAction f n g)
      (fixedLinearSystemBadLocus
        (orderedFamilyConfigurationOver f n).hom f tBase
        (orderedConfigurationSurfacePoint 𝒜 f n)
        (orderedConfigurationSurfacePoint_toBase 𝒜 f n) zeroFamily)
      (fixedLinearSystemBadLocus
        (orderedFamilyConfigurationOver f n).hom f tBase
        (orderedConfigurationSurfacePoint 𝒜 f n)
        (orderedConfigurationSurfacePoint_toBase 𝒜 f n) zeroFamily) := by
  apply mapsTo_fixedLinearSystemBadLocus_of_reindex
    (orderedFamilyConfigurationOver f n).hom f tBase
    (orderedConfigurationSurfacePoint 𝒜 f n)
    (orderedConfigurationSurfacePoint_toBase 𝒜 f n) zeroFamily
    (configurationRightAction f n g)
    (configurationRightAction_toBase f n g) g
  exact configurationRightAction_orderedConfigurationSurfacePoint 𝒜 f n g

/-- If one labelled configuration avoids a fixed line-bundle zero family,
then the generic unordered configuration avoids the image of its entire
simultaneous-zero locus. -/
theorem
    genericFunctionField_avoids_orderedConfiguration_fixedLinearSystemImage_of_exists
    [LocallyOfFiniteType f]
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    {T Z : Scheme.{u}} (tBase : T ⟶ S) [IsProper tBase]
    (zeroFamily : Z ⟶ pullback f tBase) [IsClosedImmersion zeroFamily]
    (hgood : ∃ x : (orderedFamilyConfigurationOver f n).left,
      x ∉ fixedLinearSystemBadLocus
        (orderedFamilyConfigurationOver f n).hom f tBase
        (orderedConfigurationSurfacePoint 𝒜 f n)
        (orderedConfigurationSurfacePoint_toBase 𝒜 f n) zeroFamily) :
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
        (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap 𝒜 f n ''
        fixedLinearSystemBadLocus
          (orderedFamilyConfigurationOver f n).hom f tBase
          (orderedConfigurationSurfacePoint 𝒜 f n)
          (orderedConfigurationSurfacePoint_toBase 𝒜 f n) zeroFamily := by
  apply genericFunctionField_closedPoint_avoids_projectiveConfigurationImage_of_mapsTo_of_exists
    𝒜 f n
  · exact isClosed_fixedLinearSystemBadLocus
      (orderedFamilyConfigurationOver f n).hom f tBase
      (orderedConfigurationSurfacePoint 𝒜 f n)
      (orderedConfigurationSurfacePoint_toBase 𝒜 f n) zeroFamily
  · intro g
    exact mapsTo_orderedConfiguration_fixedLinearSystemBadLocus
      𝒜 f n tBase zeroFamily g
  · exact hgood

/-- Evaluation-injective form of unordered generic avoidance.  A bad
labelled configuration must produce a nonzero section vanishing at all its
marked points; finite-dimensional evaluation supplies the one good labelled
configuration required by the quotient argument. -/
theorem
    genericFunctionField_avoids_orderedConfiguration_fixedLinearSystemImage_of_evaluation_injective
    {K P V : Type u} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Infinite P]
    [LocallyOfFiniteType f]
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    {T Z : Scheme.{u}} (tBase : T ⟶ S) [IsProper tBase]
    (zeroFamily : Z ⟶ pullback f tBase) [IsClosedImmersion zeroFamily]
    (evaluation : V →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K V ≤ n)
    (configuration : (Fin n ↪ P) →
      (orderedFamilyConfigurationOver f n).left)
    (hbad : ∀ e : Fin n ↪ P,
      configuration e ∈ fixedLinearSystemBadLocus
        (orderedFamilyConfigurationOver f n).hom f tBase
        (orderedConfigurationSurfacePoint 𝒜 f n)
        (orderedConfigurationSurfacePoint_toBase 𝒜 f n) zeroFamily →
      ∃ v : V, v ≠ 0 ∧ ∀ i, evaluation v (e i) = 0) :
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
        (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap 𝒜 f n ''
        fixedLinearSystemBadLocus
          (orderedFamilyConfigurationOver f n).hom f tBase
          (orderedConfigurationSurfacePoint 𝒜 f n)
          (orderedConfigurationSurfacePoint_toBase 𝒜 f n) zeroFamily := by
  apply genericFunctionField_avoids_orderedConfiguration_fixedLinearSystemImage_of_exists
    𝒜 f n tBase zeroFamily
  exact exists_configuration_avoids_of_evaluation_injective
    evaluation hevaluation n hrank configuration
      (fixedLinearSystemBadLocus
        (orderedFamilyConfigurationOver f n).hom f tBase
        (orderedConfigurationSurfacePoint 𝒜 f n)
        (orderedConfigurationSurfacePoint_toBase 𝒜 f n) zeroFamily) hbad

/-- Ordered generic avoidance immediately descends to the generic unordered
configuration.  This is the direct adapter from the projective-section
generic-avoidance theorem to the configuration quotient used in Voisin's
degree-eight construction. -/
theorem
    genericFunctionField_avoids_orderedConfiguration_fixedLinearSystemImage_of_orderedGeneric
    [LocallyOfFiniteType f]
    [IsIntegral (orderedFamilyConfigurationOver f n).left]
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    {T Z : Scheme.{u}} (tBase : T ⟶ S) [IsProper tBase]
    (zeroFamily : Z ⟶ pullback f tBase) [IsClosedImmersion zeroFamily]
    (hordered :
      (orderedFamilyConfigurationOver f n).left.fromSpecStalk
          (genericPoint (orderedFamilyConfigurationOver f n).left)
          (IsLocalRing.closedPoint
            (orderedFamilyConfigurationOver f n).left.functionField) ∉
        fixedLinearSystemBadLocus
          (orderedFamilyConfigurationOver f n).hom f tBase
          (orderedConfigurationSurfacePoint 𝒜 f n)
          (orderedConfigurationSurfacePoint_toBase 𝒜 f n) zeroFamily) :
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
        (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap 𝒜 f n ''
        fixedLinearSystemBadLocus
          (orderedFamilyConfigurationOver f n).hom f tBase
          (orderedConfigurationSurfacePoint 𝒜 f n)
          (orderedConfigurationSurfacePoint_toBase 𝒜 f n) zeroFamily := by
  apply genericFunctionField_avoids_orderedConfiguration_fixedLinearSystemImage_of_exists
    𝒜 f n tBase zeroFamily
  exact ⟨(orderedFamilyConfigurationOver f n).left.fromSpecStalk
      (genericPoint (orderedFamilyConfigurationOver f n).left)
      (IsLocalRing.closedPoint
        (orderedFamilyConfigurationOver f n).left.functionField), hordered⟩

/-- Morphism-level contradiction over the generic unordered configuration.
A field-valued ordered lift of that point, a common projective parameter, and
lifts of all marked points to its zero scheme place the generic quotient
point in the forbidden image of the bad locus. -/
theorem
    no_orderedConfiguration_fixedLinearSystemMember_over_unorderedGeneric_of_exists
    [LocallyOfFiniteType f]
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    {T Z : Scheme.{u}} (tBase : T ⟶ S) [IsProper tBase]
    (zeroFamily : Z ⟶ pullback f tBase) [IsClosedImmersion zeroFamily]
    (hgood : ∃ x : (orderedFamilyConfigurationOver f n).left,
      x ∉ fixedLinearSystemBadLocus
        (orderedFamilyConfigurationOver f n).hom f tBase
        (orderedConfigurationSurfacePoint 𝒜 f n)
        (orderedConfigurationSurfacePoint_toBase 𝒜 f n) zeroFamily)
    {L : Type u} [Field L]
    (r : Spec (.of L) ⟶ (orderedFamilyConfigurationOver f n).left)
    (t : Spec (.of L) ⟶ T)
    (hrt : r ≫ (orderedFamilyConfigurationOver f n).hom = t ≫ tBase)
    (hrquot : projectiveConfigurationQuotientMap 𝒜 f n
        (r (IsLocalRing.closedPoint L)) =
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
        (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField))
    (lift : Fin n → (Spec (.of L) ⟶ Z))
    (hlift : ∀ i, lift i ≫ zeroFamily =
      pullback.lift r t hrt ≫
        fixedLinearSystemIncidenceMap
          (orderedFamilyConfigurationOver f n).hom f tBase
          (orderedConfigurationSurfacePoint 𝒜 f n)
          (orderedConfigurationSurfacePoint_toBase 𝒜 f n) i) : False := by
  have havoid :=
    genericFunctionField_avoids_orderedConfiguration_fixedLinearSystemImage_of_exists
      𝒜 f n tBase zeroFamily hgood
  let z : properFiniteIncidenceParameterSpace
      (orderedFamilyConfigurationOver f n).hom tBase :=
    pullback.lift r t hrt (IsLocalRing.closedPoint L)
  let y : Fin n → Z := fun i => lift i (IsLocalRing.closedPoint L)
  have hy : ∀ i, zeroFamily (y i) =
      fixedLinearSystemIncidenceMap
        (orderedFamilyConfigurationOver f n).hom f tBase
        (orderedConfigurationSurfacePoint 𝒜 f n)
        (orderedConfigurationSurfacePoint_toBase 𝒜 f n) i z := by
    intro i
    exact congrArg (fun k => k (IsLocalRing.closedPoint L)) (hlift i)
  have hmem := mem_fixedLinearSystemBadLocus_of_parameter
    (orderedFamilyConfigurationOver f n).hom f tBase
    (orderedConfigurationSurfacePoint 𝒜 f n)
    (orderedConfigurationSurfacePoint_toBase 𝒜 f n)
    zeroFamily z y hy
  have hz : pullback.fst
      (orderedFamilyConfigurationOver f n).hom tBase z =
      r (IsLocalRing.closedPoint L) :=
    congrArg (fun k => k (IsLocalRing.closedPoint L))
      (pullback.lift_fst r t hrt)
  rw [hz] at hmem
  apply havoid
  exact ⟨r (IsLocalRing.closedPoint L), hmem, hrquot⟩

end OrderedConfigurations

end PfaffianDescent
