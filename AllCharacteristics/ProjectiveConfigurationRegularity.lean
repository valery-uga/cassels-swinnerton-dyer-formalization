import AllCharacteristics.SmoothSchemeRegularity
import AllCharacteristics.ProjectiveConfigurationBaseSmooth
import AllCharacteristics.HomogeneousConfigurationQuotient

/-!
# Regularity of the actual unordered distinct-configuration scheme

The smoothness theorem and regularity ascent apply to the original quotient
and its original base morphism. This concerns the distinct-point open; no
regularity of the full symmetric power at collisions is asserted.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
variable (f : Proj 𝒜 ⟶ S) [Smooth f] (n : ℕ)

/-- Unordered distinct configurations in a smooth projective family over a
regular affine noetherian base have regular local rings. -/
theorem isRegularLocalRing_projectiveConfigurationQuotient_stalk
    (hS : ∀ s : S, IsRegularLocalRing (S.presheaf.stalk s))
    (x : (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) :
    IsRegularLocalRing ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.presheaf.stalk x) :=
  isRegularLocalRing_stalk_of_smooth (projectiveConfigurationQuotientToBase 𝒜 f n) hS x

namespace HomogeneousProjective
variable {R : Type u} [CommRing R] {τ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule τ R)) (n : ℕ)

/-- The actual homogeneous configuration quotient is smooth over its original
noetherian coefficient ring whenever the projective family is smooth. -/
instance smooth_configurationQuotientToBase [IsNoetherianRing R] [hsm : Smooth (toBase I)] :
    Smooth (configurationQuotientToBase I n) := by
  have : Smooth (show Proj (grading I) ⟶ Spec (.of R) from toBase I) := hsm
  exact smooth_projectiveConfigurationQuotientToBase (grading I) (toBase I) n

/-- The actual homogeneous configuration quotient over a regular coefficient
ring has regular local rings when the original projective family is smooth. -/
theorem isRegularLocalRing_configurationQuotient_stalk [IsRegularRing R] [Smooth (toBase I)]
    (x : (configurationQuotientOpen I n).toScheme) :
    IsRegularLocalRing ((configurationQuotientOpen I n).toScheme.presheaf.stalk x) :=
  isRegularLocalRing_stalk_of_smooth (configurationQuotientToBase I n)
    (isRegularLocalRing_spec_stalk R) x

end HomogeneousProjective
end AllCharacteristics
