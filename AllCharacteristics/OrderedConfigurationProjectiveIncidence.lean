import AllCharacteristics.OrderedConfigurationSections
import AllCharacteristics.OrderedConfigurationMarkedAction
import AllCharacteristics.UniversalProjectiveFiniteIncidence
import AllCharacteristics.ProjectiveConfigurationGenericImageAvoidance

/-!
# Universal projective incidence on ordered configurations

The ordered distinct-configuration space has one actual map to the ambient
projective scheme for each marked point.  Applying the finite universal
incidence construction to those maps turns the statement that an equation in
a proper projective system vanishes on all marked points into a closed bad
locus on the configuration space.  This is the ordered form of the
very-general configuration step in Voisin's Lemma 3.3.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AllCharacteristics
namespace UniversalHomogeneous

universe u

variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

section OrderedConfigurations

variable {A : Type u} [CommRing A] {τ : Type u}
  [SetLike τ A] [AddSubgroupClass τ A] (𝒜 : ℕ → τ) [GradedRing 𝒜]
variable (f : Proj 𝒜 ⟶ Spec (.of R)) [IsSeparated f] (n : ℕ)

/-- The `i`th marked point of an ordered configuration, viewed in a chosen
ambient projective scheme. -/
noncomputable def orderedConfigurationProjectivePoint
    (ambient : Proj 𝒜 ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    (i : Fin n) : (orderedFamilyConfigurationOver f n).left ⟶
      Proj (MvPolynomial.homogeneousSubmodule σ R) :=
  (orderedFamilyConfigurationOpen f n).ι ≫
    (orderedFamilyCoordinate f n i).left ≫ ambient

/-- A proper family of projective equations has a closed simultaneous
vanishing locus on any integral ordered configuration space.  A single
configuration outside it therefore makes the generic configuration avoid all
of the equations' common marked-point incidences. -/
theorem genericFunctionField_closedPoint_avoids_orderedConfigurationProjectiveIncidence_of_exists
    {T : Scheme.{u}} [IsIntegral (orderedFamilyConfigurationOver f n).left]
    (ambient : Proj 𝒜 ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    (tBase : T ⟶ Spec (.of R)) [IsProper tBase]
    (s : T ⟶ projectiveParameters R σ d)
    (hgood : ∃ x : (orderedFamilyConfigurationOver f n).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus R σ d
        (orderedFamilyConfigurationOver f n).hom tBase
        (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient) s) :
    (orderedFamilyConfigurationOver f n).left.fromSpecStalk
      (genericPoint (orderedFamilyConfigurationOver f n).left)
      (IsLocalRing.closedPoint (orderedFamilyConfigurationOver f n).left.functionField) ∉
      projectiveUniversalFiniteIncidenceBadLocus R σ d
        (orderedFamilyConfigurationOver f n).hom tBase
        (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient) s :=
  genericFunctionField_closedPoint_avoids_projectiveUniversalFiniteIncidence_of_exists
    R σ d (orderedFamilyConfigurationOver f n).hom tBase
    (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient) s hgood

/-- Permuting an ordered configuration preserves the locus where one member
of a projective equation family vanishes at every marked point. -/
theorem mapsTo_orderedConfigurationProjectiveIncidenceBadLocus
    {T : Scheme.{u}}
    (ambient : Proj 𝒜 ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    (tBase : T ⟶ Spec (.of R))
    (s : T ⟶ projectiveParameters R σ d)
    (g : Equiv.Perm (Fin n)) :
    Set.MapsTo (configurationRightAction f n g)
      (projectiveUniversalFiniteIncidenceBadLocus R σ d
        (orderedFamilyConfigurationOver f n).hom tBase
        (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient) s)
      (projectiveUniversalFiniteIncidenceBadLocus R σ d
        (orderedFamilyConfigurationOver f n).hom tBase
        (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient) s) := by
  apply mapsTo_projectiveUniversalFiniteIncidenceBadLocus
    R σ d (orderedFamilyConfigurationOver f n).hom tBase
    (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient) s
    (configurationRightAction f n g)
    (configurationRightAction_toBase f n g) g
  intro i
  unfold orderedConfigurationProjectivePoint
  change configurationRightAction f n g ≫
      (((orderedFamilyConfigurationOpen f n).ι ≫
        (orderedFamilyCoordinate f n i).left) ≫ ambient) =
    ((orderedFamilyConfigurationOpen f n).ι ≫
      (orderedFamilyCoordinate f n (g i)).left) ≫ ambient
  rw [← Category.assoc]
  exact congrArg (fun h => h ≫ ambient) (configurationRightAction_coordinate f n g i)

/-- A single labelled configuration outside a finite universal-incidence
locus makes the generic *unordered* configuration avoid its image.  The
incidence condition is permutation-stable by construction, so the one
labelled witness automatically excludes its entire quotient orbit. -/
theorem genericFunctionField_closedPoint_avoids_projectiveConfigurationFiniteIncidenceImage_of_exists
    [LocallyOfFiniteType f]
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    {T : Scheme.{u}}
    (ambient : Proj 𝒜 ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    (tBase : T ⟶ Spec (.of R)) [IsProper tBase]
    (s : T ⟶ projectiveParameters R σ d)
    (hgood : ∃ x : (orderedFamilyConfigurationOver f n).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus R σ d
        (orderedFamilyConfigurationOver f n).hom tBase
        (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient) s) :
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
      (IsLocalRing.closedPoint
        (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField) ∉
      projectiveConfigurationQuotientMap 𝒜 f n ''
        projectiveUniversalFiniteIncidenceBadLocus R σ d
          (orderedFamilyConfigurationOver f n).hom tBase
          (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient) s := by
  apply AllCharacteristics.genericFunctionField_closedPoint_avoids_projectiveConfigurationImage_of_mapsTo_of_exists
    𝒜 f n
  · exact isClosed_projectiveUniversalFiniteIncidenceBadLocus R σ d
      (orderedFamilyConfigurationOver f n).hom tBase
      (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient) s
  · intro g
    exact mapsTo_orderedConfigurationProjectiveIncidenceBadLocus
      R σ d 𝒜 f n ambient tBase s g
  · exact hgood

/-- The preceding unordered-incidence avoidance works simultaneously for an
indexed family of projective systems.  The index may be the Picard group in
Voisin's argument: once each class has one labelled witness, the generic
unordered configuration avoids every corresponding closed image. -/
theorem genericFunctionField_closedPoint_avoids_projectiveConfigurationFiniteIncidenceImage_family_of_exists
    [LocallyOfFiniteType f]
    [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
    {κ : Sort v} (T : κ → Scheme.{u})
    (ambient : Proj 𝒜 ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    (tBase : ∀ c, T c ⟶ Spec (.of R))
    (hproper : ∀ c, IsProper (tBase c))
    (s : ∀ c, T c ⟶ projectiveParameters R σ d)
    (hgood : ∀ c, ∃ x : (orderedFamilyConfigurationOver f n).left,
      x ∉ projectiveUniversalFiniteIncidenceBadLocus R σ d
        (orderedFamilyConfigurationOver f n).hom (tBase c)
        (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient) (s c)) :
    ∀ c,
      (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
        (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField) ∉
        projectiveConfigurationQuotientMap 𝒜 f n ''
          projectiveUniversalFiniteIncidenceBadLocus R σ d
            (orderedFamilyConfigurationOver f n).hom (tBase c)
            (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient) (s c) := by
  intro c
  letI : IsProper (tBase c) := hproper c
  exact genericFunctionField_closedPoint_avoids_projectiveConfigurationFiniteIncidenceImage_of_exists
    R σ d 𝒜 f n ambient (tBase c) (s c) (hgood c)

/-- Forgetting one marked point maps the incidence locus for the remaining
coordinates of an `(n + 1)`-point configuration into the ordinary incidence
locus on the resulting `n`-point configuration. -/
theorem mapsTo_orderedConfigurationDelete_projectiveIncidenceBadLocus
    (ambient : Proj 𝒜 ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R))
    {T : Scheme.{u}} (tBase : T ⟶ Spec (.of R))
    (s : T ⟶ projectiveParameters R σ d)
    (i : Fin (n + 1)) :
    Set.MapsTo (Over.Hom.left (orderedFamilyConfigurationDelete f n i))
      (projectiveUniversalFiniteIncidenceBadLocus R σ d
        (orderedFamilyConfigurationOver f (n + 1)).hom tBase
        (fun j => orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f)
          (n + 1) ambient (i.succAbove j)) s)
      (projectiveUniversalFiniteIncidenceBadLocus R σ d
        (orderedFamilyConfigurationOver f n).hom tBase
        (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient) s) := by
  apply mapsTo_projectiveUniversalFiniteIncidenceBadLocus_of_maps
    R σ d
    (orderedFamilyConfigurationOver f (n + 1)).hom
    (orderedFamilyConfigurationOver f n).hom tBase
    (fun j => orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f)
      (n + 1) ambient (i.succAbove j))
    (orderedConfigurationProjectivePoint R σ (𝒜 := 𝒜) (f := f) n ambient)
    s (Over.Hom.left (orderedFamilyConfigurationDelete f n i))
  · exact (orderedFamilyConfigurationDelete f n i).w
  · intro j
    unfold orderedConfigurationProjectivePoint
    change Over.Hom.left (orderedFamilyConfigurationDelete f n i) ≫
        (Over.Hom.left (orderedFamilyConfigurationι f n) ≫
          (orderedFamilyCoordinate f n j).left ≫ ambient) =
      Over.Hom.left (orderedFamilyConfigurationι f (n + 1)) ≫
        (orderedFamilyCoordinate f (n + 1) (i.succAbove j)).left ≫ ambient
    simpa only [Category.assoc] using congrArg (fun h => h ≫ ambient)
      (orderedFamilyConfigurationDelete_coordinate f n i j)

end OrderedConfigurations

end UniversalHomogeneous
end AllCharacteristics
