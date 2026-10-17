import PfaffianDescent.VoisinDegreeElevenSerreIncidenceConfigurationFieldQuotient
import PfaffianDescent.VoisinDegreeElevenSerreIncidencePullbackNonempty

/-! # Genuine geometric integrality of the actual unordered configuration -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AllCharacteristics
namespace PfaffianDescent
universe u v
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceConfiguration_quotient_geometricallyIntegral
    {K A : Type u} [Field K] [CommRing A] {σ : Type v}
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (f : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated f]
    [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] [LocallyOfFiniteType f]
    (n : ℕ) [Nonempty (orderedFamilyConfigurationOver f n).left] :
    GeometricallyIntegral (projectiveConfigurationQuotientToBase 𝒜 f n) := by
  constructor
  intro L hL g Z fst snd h
  letI : Surjective g := (surjective_iff g).mpr (fun x =>
    ⟨IsLocalRing.closedPoint L, Subsingleton.elim _ _⟩)
  letI : Nonempty (pullback (orderedFamilyConfigurationOver f n).hom g : Scheme.{u}) :=
    serreIncidencePullback_nonempty (orderedFamilyConfigurationOver f n).hom g
  letI : IsIntegral (pullback (projectiveConfigurationQuotientToBase 𝒜 f n) g) :=
    serreIncidenceConfiguration_pullback_quotient_integral 𝒜 f g n
  exact IsIntegral.of_isIso h.isoPullback.inv

end PfaffianDescent
