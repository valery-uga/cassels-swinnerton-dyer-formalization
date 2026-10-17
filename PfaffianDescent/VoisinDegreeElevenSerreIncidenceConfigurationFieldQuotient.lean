import PfaffianDescent.VoisinDegreeElevenSerreIncidenceConfigurationFieldOpen
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFlatIntegralDescent
import AllCharacteristics.ProjectiveConfigurationBaseChangeSmooth

/-! # The actual unordered configuration quotient after integral base change -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u v
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceConfiguration_pullback_quotient_integral
    {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] {S T : Scheme.{u}}
    [IsAffine S] [IsLocallyNoetherian S] (f : Proj 𝒜 ⟶ S) [IsSeparated f]
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] [LocallyOfFiniteType f]
    (g : T ⟶ S) [IsIntegral T] [IsLocallyNoetherian T] (n : ℕ)
    [Nonempty (pullback (orderedFamilyConfigurationOver f n).hom g : Scheme.{u})] :
    IsIntegral (pullback (projectiveConfigurationQuotientToBase 𝒜 f n) g) := by
  let q := projectiveConfigurationQuotientMap 𝒜 f n
  let p := projectiveConfigurationQuotientToBase 𝒜 f n
  let r := pullback.snd q (pullback.fst p g)
  have hsource : IsIntegral (pullback (q ≫ p) g) := by
    rw [show q ≫ p = (orderedFamilyConfigurationOver f n).hom from
      projectiveConfigurationQuotientMap_toBase 𝒜 f n]
    exact serreIncidenceConfiguration_pullback_open_integral f g n
  letI : IsIntegral (pullback (q ≫ p) g) := hsource
  letI : IsIntegral (pullback q (pullback.fst p g)) :=
    IsIntegral.of_isIso (pullbackRightPullbackFstIso p g q).inv
  exact serreIncidenceFlatSurjective_integral r

end PfaffianDescent
