import AllCharacteristics.ProjectiveConfigurationIntegrality
import AllCharacteristics.ProjectiveGaloisOrbitConfiguration

/-!
# Configuration integrality from a closed point

In characteristic zero, the conjugates of a closed point form a distinct
configuration after passage to a splitting field.  Thus a closed point of
degree `n` supplies the nonemptiness input needed for integrality of the
ordered and unordered degree-`n` configuration spaces.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics

universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A characteristic-zero closed point of degree `n` gives a point of its
unordered distinct-configuration quotient. -/
theorem nonempty_projectiveConfigurationQuotientOpen_of_closedPoint
    {K : Type u} [Field K] [CharZero K]
    (g : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated g] [LocallyOfFiniteType g]
    (x : closedPoints (Proj 𝒜)) (n : ℕ)
    (hx : g.residueDegree x.1 = n) :
    Nonempty (projectiveConfigurationQuotientOpen 𝒜 g n).toScheme := by
  obtain ⟨c, -⟩ := exists_projectiveConfigurationPoint_of_closedPoint 𝒜 g x n hx
  exact ⟨c (IsLocalRing.closedPoint K)⟩

/-- A characteristic-zero closed point of degree `n` makes the corresponding
ordered distinct-configuration scheme nonempty. -/
theorem nonempty_orderedFamilyConfigurationOver_of_closedPoint
    {K : Type u} [Field K] [CharZero K]
    (g : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated g] [LocallyOfFiniteType g]
    (x : closedPoints (Proj 𝒜)) (n : ℕ)
    (hx : g.residueDegree x.1 = n) :
    Nonempty (orderedFamilyConfigurationOver g n).left := by
  obtain ⟨c⟩ := nonempty_projectiveConfigurationQuotientOpen_of_closedPoint 𝒜 g x n hx
  obtain ⟨a, -⟩ := (projectiveConfigurationQuotientMap 𝒜 g n).surjective
    c
  exact ⟨a⟩

/-- Under geometric integrality, a degree-`n` closed point supplies all
nonemptiness needed to make its unordered configuration quotient integral. -/
theorem isIntegral_projectiveConfigurationQuotientOpen_of_closedPoint
    {K : Type u} [Field K] [CharZero K]
    (g : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated g] [Smooth g] [GeometricallyIntegral g]
    (x : closedPoints (Proj 𝒜)) (n : ℕ)
    (hx : g.residueDegree x.1 = n) :
    IsIntegral (projectiveConfigurationQuotientOpen 𝒜 g n).toScheme := by
  letI : Nonempty (orderedFamilyConfigurationOver g n).left :=
    nonempty_orderedFamilyConfigurationOver_of_closedPoint 𝒜 g x n hx
  exact isIntegral_projectiveConfigurationQuotientOpen_of_geometricallyIntegral 𝒜 g n

end AllCharacteristics
