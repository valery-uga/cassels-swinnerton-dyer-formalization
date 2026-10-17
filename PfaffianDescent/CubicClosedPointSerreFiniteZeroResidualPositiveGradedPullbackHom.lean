import PfaffianDescent.CubicPointTraceFieldBaseChangeGradedTwistHom
import PfaffianDescent.VoisinHypersurfacePositiveTwist
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
variable {A B ρ τ : Type u} [CommRing A] [CommRing B]
  [SetLike ρ A] [AddSubgroupClass ρ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒢 : ℕ → ρ) (ℋ : ℕ → τ) [GradedRing 𝒢] [GradedRing ℋ]
theorem gradedRingHomPositiveTwistToPushforward_positiveMulHomogeneous
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤ (HomogeneousIdeal.irrelevant 𝒢).map f)
    {d : ℕ} (s : 𝒢 d) (m : ℕ) :
    positiveMulHomogeneous 𝒢 s m ≫ gradedRingHomPositiveTwistToPushforward 𝒢 ℋ f hf (m + d) =
    gradedRingHomPositiveTwistToPushforward 𝒢 ℋ f hf m ≫
      (Scheme.Modules.pushforward (Proj.map f hf)).map
        (positiveMulHomogeneous ℋ ⟨f s, f.2 s.2⟩ m) := by
  ext U z
  apply Subtype.ext
  funext y
  change Localization.localRingHom
    (positivePointIdeal 𝒢 (Proj.map f hf y.1)) (positivePointIdeal ℋ y.1) f.toRingHom rfl
      (algebraMap A (PositiveFiber 𝒢 (Proj.map f hf y.1)) (s : A) *
        z.1 ⟨Proj.map f hf y.1, y.2⟩) =
    algebraMap B (PositiveFiber ℋ y.1) (f s : B) *
      Localization.localRingHom
        (positivePointIdeal 𝒢 (Proj.map f hf y.1)) (positivePointIdeal ℋ y.1) f.toRingHom rfl
        (z.1 ⟨Proj.map f hf y.1, y.2⟩)
  rw [map_mul]
  congr 1
  rw [← Localization.mk_one_eq_algebraMap, Localization.localRingHom_mk]
  rw [← Localization.mk_one_eq_algebraMap]
  congr 1
  apply Subtype.ext
  exact f.toRingHom.map_one


theorem cubicClosedPointSerreFiniteZeroResidual_positiveGradedPushforward_zero
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤ (HomogeneousIdeal.irrelevant 𝒢).map f) :
    gradedRingHomPositiveTwistToPushforward 𝒢 ℋ f hf 0 ≫
      (Scheme.Modules.pushforward (Proj.map f hf)).map (positiveZeroTwistIso ℋ).hom =
    (positiveZeroTwistIso 𝒢).hom ≫ gradedRingHomTwistToPushforward 𝒢 ℋ f hf 0 := by
  ext U z
  apply Subtype.ext
  funext y
  rfl

def cubicClosedPointSerreFiniteZeroResidual_positiveGradedPullbackHom
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤ (HomogeneousIdeal.irrelevant 𝒢).map f)
    (m : ℕ) :
    (Scheme.Modules.pullback (Proj.map f hf)).obj (positiveSheafOfModules 𝒢 m) ⟶
      positiveSheafOfModules ℋ m :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).homEquiv _ _).symm
    (gradedRingHomPositiveTwistToPushforward 𝒢 ℋ f hf m)

end PfaffianDescent.ProjectiveNegativeTwist
