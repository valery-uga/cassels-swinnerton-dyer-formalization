import PfaffianDescent.CubicPointTraceFieldBaseChangeGradedTwistHom
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

/-- The adjoint graded zero-twist map is the actual pullback-unit comparison
under the canonical zero-twist maps. -/
theorem cubicPointTraceFieldBaseChangeGradedTwistPullbackHom_zero :
    (Scheme.Modules.pullback (Proj.map f hf)).map (unitToZeroTwist 𝒢) ≫
      cubicPointTraceFieldBaseChangeGradedTwistPullbackHom 𝒢 ℋ f hf 0 =
    BundleSectionZeroLocus.pullbackUnitComparison (Proj.map f hf) ≫
      unitToZeroTwist ℋ := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)
  have h := congrArg
    (fun t : SheafOfModules.unit (Proj 𝒢).ringCatSheaf ⟶
      (Scheme.Modules.pushforward (Proj.map f hf)).obj (sheafOfModules ℋ 0) =>
        (adj.homEquiv _ _).symm t)
    (cubicPointTraceFieldBaseChangeGradedTwistToPushforward_zero 𝒢 ℋ f hf)
  rw [adj.homEquiv_naturality_left_symm,
    adj.homEquiv_naturality_right_symm] at h
  exact h

/-- Actual pullback of the zero twist is canonically the zero twist. -/
theorem cubicPointTraceFieldBaseChangeGradedTwistPullbackHom_zero_isIso :
    IsIso (cubicPointTraceFieldBaseChangeGradedTwistPullbackHom 𝒢 ℋ f hf 0) := by
  letI := unitToZeroTwist_isIso 𝒢
  letI := unitToZeroTwist_isIso ℋ
  letI := BundleSectionZeroLocus.isIso_pullbackUnitComparison (Proj.map f hf)
  let P := Scheme.Modules.pullback (Proj.map f hf)
  haveI : IsIso (P.map (unitToZeroTwist 𝒢) ≫
      cubicPointTraceFieldBaseChangeGradedTwistPullbackHom 𝒢 ℋ f hf 0) := by
    rw [cubicPointTraceFieldBaseChangeGradedTwistPullbackHom_zero]
    infer_instance
  exact IsIso.of_isIso_comp_left (P.map (unitToZeroTwist 𝒢)) _

/-- Actual pullback intertwines homogeneous multiplication on the two
intrinsic negative twists. -/
theorem cubicPointTraceFieldBaseChangeGradedTwistPullbackHom_mul
    {d : ℕ} (s : 𝒢 d) (m : ℕ) :
    (Scheme.Modules.pullback (Proj.map f hf)).map (mulHomogeneous 𝒢 s m) ≫
      cubicPointTraceFieldBaseChangeGradedTwistPullbackHom 𝒢 ℋ f hf m =
    cubicPointTraceFieldBaseChangeGradedTwistPullbackHom 𝒢 ℋ f hf (m + d) ≫
      mulHomogeneous ℋ ⟨f s, f.2 s.2⟩ m := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)
  have h := congrArg
    (fun t : sheafOfModules 𝒢 (m + d) ⟶
      (Scheme.Modules.pushforward (Proj.map f hf)).obj (sheafOfModules ℋ m) =>
        (adj.homEquiv _ _).symm t)
    (gradedRingHomTwistToPushforward_mulHomogeneous 𝒢 ℋ f hf s m)
  rw [adj.homEquiv_naturality_left_symm,
    adj.homEquiv_naturality_right_symm] at h
  exact h

end PfaffianDescent.ProjectiveNegativeTwist
