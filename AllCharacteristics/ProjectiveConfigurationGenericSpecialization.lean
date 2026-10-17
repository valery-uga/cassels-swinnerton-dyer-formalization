import AllCharacteristics.ProperFamilyGenericPointSpecialization
import AllCharacteristics.ProjectiveConfigurationRegularity
import AllCharacteristics.ProjectiveConfigurationIntegrality

/-!
# Specialization from a generic unordered configuration

This is the specialization step used after Voisin's construction has been
performed at the generic point of an unordered configuration space.  Its
regularity hypothesis is discharged by the proved smoothness of the actual
configuration quotient.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AllCharacteristics
universe u v

variable {A : Type u} [CommRing A] {sigma : Type v} [SetLike sigma A]
  [AddSubgroupClass sigma A]
variable (graded : ℕ → sigma) [GradedRing graded]
variable {K : Type u} [Field K]
variable (f : Proj graded ⟶ Spec (.of K)) [IsProper f] [Smooth f]

/-- A generic point of an irreducible space belongs to a closed subset exactly
when that subset is the whole space.  This is the topological form of the
``very general configuration avoids a proper closed condition'' step used in
Voisin's argument. -/
theorem genericPoint_mem_closed_iff_eq_univ
    {X : Type u} [TopologicalSpace X] [QuasiSober X] [IrreducibleSpace X]
    {Z : Set X} (hZ : IsClosed Z) :
    genericPoint X ∈ Z ↔ Z = Set.univ := by
  constructor
  · intro hx
    have hsub : (Set.univ : Set X) ⊆ Z :=
      ((genericPoint_spec X).mem_closed_set_iff hZ).mp hx
    exact Set.eq_univ_of_forall fun x ↦ hsub (Set.mem_univ x)
  · rintro rfl
    exact Set.mem_univ _

/-- The generic point simultaneously avoids every member of any family of
proper closed subsets.  No countability hypothesis is required for this
generic-point formulation; constructing the closed bad loci remains the
geometric content of the application. -/
theorem genericPoint_avoids_proper_closed_family
    {X : Type u} [TopologicalSpace X] [QuasiSober X] [IrreducibleSpace X]
    {ι : Sort v} (Z : ι → Set X)
    (hclosed : ∀ i, IsClosed (Z i)) (hproper : ∀ i, Z i ≠ Set.univ) :
    ∀ i, genericPoint X ∉ Z i := by
  intro i hi
  exact hproper i (genericPoint_mem_closed_iff_eq_univ (hclosed i) |>.mp hi)

/-- The generic point of an integral scheme avoids every proper closed
condition.  This is the form used by an integral configuration scheme. -/
theorem genericPoint_avoids_proper_closed_of_isIntegral
    (X : Scheme.{u}) [IsIntegral X] {Z : Set X}
    (hclosed : IsClosed Z) (hproper : Z ≠ Set.univ) :
    genericPoint X ∉ Z :=
  genericPoint_avoids_proper_closed_family (fun _ : Unit ↦ Z)
    (fun _ ↦ hclosed) (fun _ ↦ hproper) ()

/-- The closed point of the generic function-field map is the generic point
of the integral parameter scheme, and therefore avoids each proper closed
bad locus.  This bridges closed-locus constructions directly to the actual
function-field configuration used in specialization arguments. -/
theorem genericFunctionField_closedPoint_avoids_proper_closed
    (X : Scheme.{u}) [IsIntegral X] {Z : Set X}
    (hclosed : IsClosed Z) (hproper : Z ≠ Set.univ) :
    X.fromSpecStalk (genericPoint X)
      (IsLocalRing.closedPoint X.functionField) ∉ Z := by
  simpa only [Scheme.fromSpecStalk_closedPoint] using
    (genericPoint_avoids_proper_closed_of_isIntegral X hclosed hproper)

/-- The closed point of the generic function-field map avoids every member
of an indexed family of proper closed conditions.  This is the generic-point
replacement for the countability argument in Voisin's use of `Pic(S)`: once
the bad locus has been constructed for each divisor class, the generic
configuration avoids each of them separately. -/
theorem genericFunctionField_closedPoint_avoids_proper_closed_family
    (X : Scheme.{u}) [IsIntegral X] {ι : Sort v} (Z : ι → Set X)
    (hclosed : ∀ i, IsClosed (Z i)) (hproper : ∀ i, Z i ≠ Set.univ) :
    ∀ i, X.fromSpecStalk (genericPoint X)
      (IsLocalRing.closedPoint X.functionField) ∉ Z i := by
  intro i
  simpa only [Scheme.fromSpecStalk_closedPoint] using
    (genericPoint_avoids_proper_closed_family Z hclosed hproper i)

/-- A closed incidence condition parametrized by a proper scheme has closed
image.  If that image is proper, the actual generic function-field point of
an integral base avoids it.  This is the form needed to turn a projective
space of sections and its universal vanishing locus into a bad locus for a
generic configuration. -/
theorem genericFunctionField_closedPoint_avoids_proper_incidenceImage
    (B T : Scheme.{u}) [IsIntegral B] (π : T ⟶ B) [IsProper π]
    {I : Set T} (hclosed : IsClosed I) (hproper : π '' I ≠ Set.univ) :
    B.fromSpecStalk (genericPoint B)
      (IsLocalRing.closedPoint B.functionField) ∉ π '' I :=
  genericFunctionField_closedPoint_avoids_proper_closed B
    (π.isClosedMap I hclosed) hproper

/-- The generic configuration avoids every member of an indexed collection
of proper closed incidence images.  The parameter schemes may vary with the
index; this is the form needed when a divisor class determines both a linear
system and its incidence correspondence. -/
theorem genericFunctionField_closedPoint_avoids_proper_incidenceImage_family
    (B : Scheme.{u}) [IsIntegral B] {ι : Sort v}
    (T : ι → Scheme.{u}) (π : ∀ i, T i ⟶ B)
    (hπ : ∀ i, IsProper (π i)) (I : ∀ i, Set (T i))
    (hclosed : ∀ i, IsClosed (I i))
    (hproper : ∀ i, π i '' I i ≠ Set.univ) :
    ∀ i, B.fromSpecStalk (genericPoint B)
      (IsLocalRing.closedPoint B.functionField) ∉ π i '' I i := by
  intro i
  letI : IsProper (π i) := hπ i
  exact genericFunctionField_closedPoint_avoids_proper_incidenceImage
    B (T i) (π i) (hclosed i) (hproper i)

/-- If the projective family acquires a point over the function field of its
integral unordered distinct-configuration space, that point specializes at
every field-valued configuration. -/
theorem proper_point_of_projectiveConfiguration_functionField_point
    (n : ℕ)
    [IsIntegral (projectiveConfigurationQuotientOpen graded f n).toScheme]
    (c : Spec (.of K) ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _)
    (s : Spec (projectiveConfigurationQuotientOpen graded f n).toScheme.functionField ⟶
      Proj graded)
    (hs : s ≫ f =
      (projectiveConfigurationQuotientOpen graded f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen graded f n).toScheme) ≫
        projectiveConfigurationQuotientToBase graded f n) :
    ∃ q : Spec (.of K) ⟶ Proj graded, q ≫ f = 𝟙 _ := by
  let B := (projectiveConfigurationQuotientOpen graded f n).toScheme
  let b := projectiveConfigurationQuotientToBase graded f n
  let x := c (IsLocalRing.closedPoint K)
  haveI : IsRegularLocalRing (B.presheaf.stalk x) :=
    isRegularLocalRing_projectiveConfigurationQuotient_stalk graded f n
      (fun y ↦ isRegularLocalRing_spec_stalk K y) x
  exact proper_point_of_parameter_functionField_point b f c hc s hs

/-- The same specialization theorem with integrality supplied by the ordered
configuration space.  The quotient integrality is proved by the affine
invariant-chart construction, so callers need not assume it independently. -/
theorem proper_point_of_projectiveConfiguration_functionField_point_of_orderedIntegral
    (n : ℕ)
    [IsIntegral (orderedFamilyConfigurationOver f n).left]
    (c : Spec (.of K) ⟶
      (projectiveConfigurationQuotientOpen graded f n).toScheme)
    (hc : c ≫ projectiveConfigurationQuotientToBase graded f n = 𝟙 _)
    (s : Spec (projectiveConfigurationQuotientOpen graded f n).toScheme.functionField ⟶
      Proj graded)
    (hs : s ≫ f =
      (projectiveConfigurationQuotientOpen graded f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen graded f n).toScheme) ≫
        projectiveConfigurationQuotientToBase graded f n) :
    ∃ q : Spec (.of K) ⟶ Proj graded, q ≫ f = 𝟙 _ := by
  exact proper_point_of_projectiveConfiguration_functionField_point
    graded f n c hc s hs

end AllCharacteristics
