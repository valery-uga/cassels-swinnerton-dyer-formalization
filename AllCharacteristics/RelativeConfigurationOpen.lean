import AllCharacteristics.RelativeOrderedTuples
import AllCharacteristics.FieldPointClosedLocus

/-!
# The distinct-point open in an ordered relative power

For a separated family, each pairwise coincidence locus is closed. Their
finite complement defines an actual open scheme. Field-valued membership
means that the coordinate maps are pairwise distinct over the same field.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AllCharacteristics
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]

/-- Pairwise coordinate coincidence is an actual closed subscheme of the ordered power. -/
instance isClosedImmersion_orderedFamilyCoincidence (n : ℕ) (i j : Fin n) :
    IsClosedImmersion (equalizer.ι (orderedFamilyCoordinate f n i)
      (orderedFamilyCoordinate f n j)).left :=
  @isClosedImmersion_equalizer_ι_left S (orderedFamilyPowerOver f n) (Over.mk f)
    (show IsSeparated f from inferInstance)
    (orderedFamilyCoordinate f n i) (orderedFamilyCoordinate f n j)

/-- The open where two coordinates avoid their scheme-theoretic coincidence locus. -/
noncomputable def orderedFamilyDistinctPairOpen (n : ℕ) (i j : Fin n) :
    (orderedFamilyPowerOver f n).left.Opens :=
  ⟨(Set.range (equalizer.ι (orderedFamilyCoordinate f n i)
    (orderedFamilyCoordinate f n j)).left)ᶜ,
    (Scheme.Hom.isClosedEmbedding _).isClosed_range.isOpen_compl⟩

/-- The actual open of ordered pairwise distinct points of the family. -/
noncomputable def orderedFamilyConfigurationOpen (n : ℕ) :
    (orderedFamilyPowerOver f n).left.Opens :=
  ⨅ i : Fin n, ⨅ j : Fin n, if i = j then ⊤ else orderedFamilyDistinctPairOpen f n i j

/-- Membership in the configuration open avoids every off-diagonal coincidence locus. -/
theorem mem_orderedFamilyConfigurationOpen_iff (n : ℕ) (x : (orderedFamilyPowerOver f n).left) :
    x ∈ orderedFamilyConfigurationOpen f n ↔
      ∀ i j : Fin n, i ≠ j →
        x ∉ Set.range (equalizer.ι (orderedFamilyCoordinate f n i)
          (orderedFamilyCoordinate f n j)).left := by
  change x ∈ ((orderedFamilyConfigurationOpen f n :
    (orderedFamilyPowerOver f n).left.Opens) : Set _) ↔ _
  simp only [orderedFamilyConfigurationOpen, Opens.coe_iInf, Set.mem_iInter]
  constructor
  · intro h i j hij
    have hh := h i j
    rw [if_neg hij] at hh
    exact hh
  · intro h i j
    by_cases hij : i = j
    · simp only [if_pos hij, Opens.coe_top, Set.mem_univ]
    · rw [if_neg hij]
      exact h i j hij

/-- A field-valued tuple lies on a coincidence locus exactly when its two
coordinate morphisms are equal over that same field. -/
theorem fieldTuple_mem_coincidence_iff (n : ℕ) (i j : Fin n)
    {k : Type u} [Field k] (b : Spec (.of k) ⟶ S)
    (a : Over.mk b ⟶ orderedFamilyPowerOver f n) :
    a.left (IsLocalRing.closedPoint k) ∈ Set.range
      (equalizer.ι (orderedFamilyCoordinate f n i) (orderedFamilyCoordinate f n j)).left ↔
        a ≫ orderedFamilyCoordinate f n i = a ≫ orderedFamilyCoordinate f n j := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := (fieldPoint_mem_closed_range_iff
      (equalizer.ι (orderedFamilyCoordinate f n i) (orderedFamilyCoordinate f n j)).left
      (a.left : Spec (.of k) ⟶ (orderedFamilyPowerOver f n).left)).mp h
    apply Over.OverMorphism.ext
    have hc := congrArg (fun c ↦ Over.Hom.left c)
      (equalizer.condition (orderedFamilyCoordinate f n i) (orderedFamilyCoordinate f n j))
    change Over.Hom.left (equalizer.ι (orderedFamilyCoordinate f n i)
      (orderedFamilyCoordinate f n j)) ≫ Over.Hom.left (orderedFamilyCoordinate f n i) =
      Over.Hom.left (equalizer.ι (orderedFamilyCoordinate f n i)
        (orderedFamilyCoordinate f n j)) ≫ Over.Hom.left (orderedFamilyCoordinate f n j) at hc
    change Over.Hom.left a ≫ Over.Hom.left (orderedFamilyCoordinate f n i) =
      Over.Hom.left a ≫ Over.Hom.left (orderedFamilyCoordinate f n j)
    rw [← hr, Category.assoc, hc]
    exact (Category.assoc _ _ _).symm
  · intro h
    apply (fieldPoint_mem_closed_range_iff
      (equalizer.ι (orderedFamilyCoordinate f n i) (orderedFamilyCoordinate f n j)).left
      (a.left : Spec (.of k) ⟶ (orderedFamilyPowerOver f n).left)).mpr
    exact ⟨(equalizer.lift a h).left, congrArg (fun c ↦ c.left) (equalizer.lift_ι a h)⟩

/-- Field-valued points of the configuration open are precisely the tuples
whose coordinate maps are pairwise distinct. -/
theorem fieldTuple_mem_configuration_iff (n : ℕ)
    {k : Type u} [Field k] (b : Spec (.of k) ⟶ S)
    (a : Over.mk b ⟶ orderedFamilyPowerOver f n) :
    a.left (IsLocalRing.closedPoint k) ∈ orderedFamilyConfigurationOpen f n ↔
      ∀ i j : Fin n, i ≠ j →
        a ≫ orderedFamilyCoordinate f n i ≠ a ≫ orderedFamilyCoordinate f n j := by
  rw [mem_orderedFamilyConfigurationOpen_iff]
  simp only [fieldTuple_mem_coincidence_iff]

/-- The ordered configuration space with its actual structure map to the base. -/
noncomputable def orderedFamilyConfigurationOver (n : ℕ) : Over S :=
  Over.mk ((orderedFamilyConfigurationOpen f n).ι ≫ (orderedFamilyPowerOver f n).hom)

/-- Ordered configurations in a smooth separated family remain smooth over the base. -/
instance smooth_orderedFamilyConfiguration (n : ℕ) [Smooth f] :
    Smooth (orderedFamilyConfigurationOver f n).hom := by
  change Smooth ((orderedFamilyConfigurationOpen f n).ι ≫ (orderedFamilyPowerOver f n).hom)
  infer_instance

/-- A nonempty distinct-configuration open in an integral ordered power is
integral.  The nonemptiness condition records the substantive geometric
requirement that the family has enough pairwise distinct points. -/
theorem isIntegral_orderedFamilyConfigurationOver_of_geometricallyIntegral
    (n : ℕ) [Nonempty (orderedFamilyConfigurationOver f n).left]
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] [LocallyOfFiniteType f]
    [IsIntegral S] [IsLocallyNoetherian S] :
    IsIntegral (orderedFamilyConfigurationOver f n).left := by
  letI : IsIntegral (orderedFamilyPowerOver f n).left :=
    isIntegral_orderedFamilyPower_of_geometricallyIntegral f n
  letI : Nonempty (orderedFamilyConfigurationOpen f n).toScheme := by
    change Nonempty (orderedFamilyConfigurationOver f n).left
    infer_instance
  change IsIntegral (orderedFamilyConfigurationOpen f n).toScheme
  infer_instance

end AllCharacteristics
