import PfaffianDescent.CubicClosedPointSerrePointSplittingConfiguration
import PfaffianDescent.CubicClosedPointSerrePointSplittingComposite

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

/-- Exact component projection, with its native type inferred to avoid
re-expanding the projective configuration diagram during type checking. -/
abbrev pointSplittingConfigurationIso_component_fst (i : Fin n) := by
  let g := (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
    (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
  let q := (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
    pullback.snd (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) g
  let e := projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n
  let a := projectiveConfigurationIncidenceFiberIsoConstantCover 𝒜 f n r
  have h := pointSplittingPullbackIso_congrHom_fst
    (projectiveConfigurationIncidenceToBase 𝒜 f n) g
    (Spec.map (CommRingCat.ofHom b)) (r ≫ projectiveConfigurationQuotientMap 𝒜 f n)
    hb.symm q e (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber_hom_snd 𝒜 f n)
  exact congrArg (fun t => Sigma.ι (fun _ : ULift.{u} (Fin n) ↦ Spec (.of E))
    (ULift.up i) ≫ a.hom ≫ t) h

/-- The same native split scheme comparison is over the extension field. -/
abbrev pointSplittingConfigurationIso_hom_snd := by
  let g := (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme.fromSpecStalk
    (genericPoint (projectiveConfigurationQuotientOpen 𝒜 f n).toScheme)
  let q := (projectiveConfigurationGenericFiniteSubscheme 𝒜 f n).val.subschemeι ≫
    pullback.snd (pullback.snd f (projectiveConfigurationQuotientToBase 𝒜 f n)) g
  let e := projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber 𝒜 f n
  let a := projectiveConfigurationIncidenceFiberIsoConstantCover 𝒜 f n r
  have h := pointSplittingPullbackIso_congrHom_snd
    (projectiveConfigurationIncidenceToBase 𝒜 f n) g
    (Spec.map (CommRingCat.ofHom b)) (r ≫ projectiveConfigurationQuotientMap 𝒜 f n)
    hb.symm q e (projectiveConfigurationGenericFiniteSubschemeIsoIncidenceFiber_hom_snd 𝒜 f n)
  exact (congrArg (fun t => a.hom ≫ t) h).trans
    (projectiveConfigurationIncidenceFiberIsoConstantCover_hom_snd 𝒜 f n r)

end PfaffianDescent
