import AllCharacteristics.ProjectiveConfigurationAffineCharts

/-!
# The categorical universal property of the projective configuration quotient

Stable affine neighborhoods inside the original common-affine charts supply
actual free invariant-spectrum quotient charts. Their maps restrict through
the original configuration pullback square. The proved affine factorization
and gluing results therefore apply to arbitrary scheme targets.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] (f : Proj 𝒜 ⟶ S) (n : ℕ)

/-- Every permutation-invariant morphism from the original ordered distinct
configurations factors uniquely through their actual projective quotient,
for any target scheme and in every characteristic. -/
theorem existsUnique_projectiveConfigurationFactor {T : Scheme.{u}}
    (a : (orderedFamilyConfigurationOver f n).left ⟶ T)
    (ha : ∀ g : Equiv.Perm (Fin n), configurationRightAction f n g ≫ a = a) :
    ∃! b : (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme ⟶ T,
      projectiveConfigurationQuotientMap 𝒜 f n ≫ b = a := by
  let G := Equiv.Perm (Fin n)
  refine existsUnique_freeQuotientChartFactor (S := S) G (configurationRightAction f n)
    (configurationRightAction_one f n) (configurationRightAction_mul f n)
    (projectiveConfigurationQuotientMap 𝒜 f n)
    (projectiveConfigurationQuotientMap_eq_iff_orbit 𝒜 f n)
    (fun K _ c g hg ↦ configurationRightAction_no_fixed_field_point f n K c g hg) ?_ a ha
  intro x
  obtain ⟨U, hUa, τ, hτ₁, hτcomp, i, hio, hi, p, hp, j, hjo, hx, hs, _⟩ :=
    exists_projectiveConfigurationQuotient_affineChart 𝒜 f n x
  exact ⟨U, hUa, τ, hτ₁, hτcomp, i, hio, hi, p, hp, j, hjo, hx, hs⟩

end AllCharacteristics
