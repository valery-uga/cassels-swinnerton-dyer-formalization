import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPositiveGradedPullbackHom
import PfaffianDescent.CubicPointTraceFieldBaseChangeGradedTwistPullback
import PfaffianDescent.CubicPointTraceFieldBaseChangePullbackRestrict
import PfaffianDescent.SchemeModuleOpenCoverIso

/-! # Actual negative-twist pullback squares -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false

variable {A B ρ τ : Type u} [CommRing A] [CommRing B]
  [SetLike ρ A] [AddSubgroupClass ρ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒢 : ℕ → ρ) (ℋ : ℕ → τ) [GradedRing 𝒢] [GradedRing ℋ]
  (f : 𝒢 →+*ᵍ ℋ)
  (hf : HomogeneousIdeal.irrelevant ℋ ≤ (HomogeneousIdeal.irrelevant 𝒢).map f)

theorem cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom_zero :
    cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom 𝒢 ℋ f hf 0 ≫
      (positiveZeroTwistIso ℋ).hom =
    (Scheme.Modules.pullback (Proj.map f hf)).map (positiveZeroTwistIso 𝒢).hom ≫
      cubicPointTraceFieldBaseChangeGradedTwistPullbackHom 𝒢 ℋ f hf 0 := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)
  have h := congrArg
    (fun t : positiveSheafOfModules 𝒢 0 ⟶
      (Scheme.Modules.pushforward (Proj.map f hf)).obj (sheafOfModules ℋ 0) =>
        (adj.homEquiv _ _).symm t)
    (cubicClosedPointSerreFiniteZeroResidual_positiveGradedPushforward_zero 𝒢 ℋ f hf)
  rw [adj.homEquiv_naturality_right_symm, adj.homEquiv_naturality_left_symm] at h
  exact h

theorem cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom_zero_isIso :
    IsIso (cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom 𝒢 ℋ f hf 0) := by
  let P := Scheme.Modules.pullback (Proj.map f hf)
  letI := cubicPointTraceFieldBaseChangeGradedTwistPullbackHom_zero_isIso 𝒢 ℋ f hf
  haveI : IsIso (cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom 𝒢 ℋ f hf 0 ≫
      (positiveZeroTwistIso ℋ).hom) := by
    rw [cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom_zero]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (positiveZeroTwistIso ℋ).hom

theorem cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom_mul
    {d : ℕ} (s : 𝒢 d) (m : ℕ) :
    (Scheme.Modules.pullback (Proj.map f hf)).map (positiveMulHomogeneous 𝒢 s m) ≫
      cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom 𝒢 ℋ f hf (m + d) =
    cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom 𝒢 ℋ f hf m ≫
      positiveMulHomogeneous ℋ ⟨f s, f.2 s.2⟩ m := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)
  have h := congrArg
    (fun t : positiveSheafOfModules 𝒢 m ⟶
      (Scheme.Modules.pushforward (Proj.map f hf)).obj (positiveSheafOfModules ℋ (m+d)) =>
        (adj.homEquiv _ _).symm t)
    (gradedRingHomPositiveTwistToPushforward_positiveMulHomogeneous 𝒢 ℋ f hf s m)
  rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm] at h
  exact h

end PfaffianDescent.ProjectiveNegativeTwist
