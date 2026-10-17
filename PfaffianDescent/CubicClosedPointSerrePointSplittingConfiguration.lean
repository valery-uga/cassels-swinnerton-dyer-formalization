import PfaffianDescent.CubicClosedPointSerrePointSplittingPullback

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics
namespace PfaffianDescent
universe u v
set_option backward.isDefEq.respectTransparency false
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {K : Type u} [Field K] (f : Proj 𝒜 ⟶ Spec (.of K)) [IsSeparated f]
variable (n : ℕ) [IsIntegral (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme]
variable {E : Type u} [Field E]
variable (r : Spec (.of E) ⟶ (orderedFamilyConfigurationOver f n).left)
variable (b : (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.functionField →+* E)
variable (hb : Spec.map (CommRingCat.ofHom b) ≫
    (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
      (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme) =
    r ≫ projectiveConfigurationQuotientMap 𝒜 f n)

/-- The actual generic unordered finite configuration, after scalar extension
along the ordered lift, is the disjoint union of its labeled spectra. -/
def pointSplittingConfigurationIso :
    (∐ fun _ : ULift.{u} (Fin n) ↦ Spec (.of E)) ≅
    pullback ((projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
      pullback.snd (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n))
        ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)))
      (Spec.map (CommRingCat.ofHom b)) :=
  projectiveConfigurationIncidenceFiberIsoConstantCover 𝒜 f n r ≪≫
    pullback.congrHom rfl hb.symm ≪≫
    pointSplittingPullbackIso (projectiveConfigurationIncidenceToBase 𝒜 f n)
      ((projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
        (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme))
      (Spec.map (CommRingCat.ofHom b)) _
      (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n)
      (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber_hom_snd 𝒜 f n)

end PfaffianDescent
