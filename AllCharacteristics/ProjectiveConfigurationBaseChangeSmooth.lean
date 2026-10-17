import AllCharacteristics.ConfigurationBaseChangeSmooth
import AllCharacteristics.EtaleSchemeSourceSmooth
import AllCharacteristics.ProjectiveTupleQuotientFinitePresentation

/-! # Smoothness of the configuration quotient after base change

If a base change of the original projective family is smooth, the same base
change of its actual distinct-configuration quotient is smooth. This is
proved using the pulled-back ordered cover, without assuming a comparison
between different quotient constructions.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {S : Scheme.{u}} [IsAffine S] [IsLocallyNoetherian S]
variable (f : Proj 𝒜 ⟶ S) [LocallyOfFiniteType f] (n : ℕ)

/-- The actual unordered distinct-configuration quotient is smooth after
any base change making the original projective family smooth. -/
lemma smooth_pullback_projectiveConfigurationQuotient
    {T : Scheme.{u}} (g : T ⟶ S) [Smooth (pullback.snd f g)] :
    Smooth (pullback.snd (projectiveConfigurationQuotientToBase 𝒜 f n) g) := by
  let q := projectiveConfigurationQuotientMap 𝒜 f n
  let p := projectiveConfigurationQuotientToBase 𝒜 f n
  let r := pullback.snd q (pullback.fst p g)
  have : Smooth (pullback.snd (q ≫ p) g) := by
    rw [show q ≫ p = (orderedFamilyConfigurationOver f n).hom from
      projectiveConfigurationQuotientMap_toBase 𝒜 f n]
    exact smooth_pullback_orderedFamilyConfiguration f g n
  have : Smooth (r ≫ pullback.snd p g) := by
    change Smooth (pullback.snd q (pullback.fst p g) ≫ pullback.snd p g)
    rw [← pullbackRightPullbackFstIso_hom_snd p g q]
    infer_instance
  exact smooth_of_surjective_etale_affine_source r (pullback.snd p g)

end AllCharacteristics
