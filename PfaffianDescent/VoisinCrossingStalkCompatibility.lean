import PfaffianDescent.ProjectiveCrossingTwist
import PfaffianDescent.VoisinHypersurfacePositiveTwist

/-! # Restriction compatibility for crossing twist multiplication -/

noncomputable section

namespace PfaffianDescent

open scoped DirectSum Pointwise
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

universe u

namespace ProjectiveNegativeTwist

variable {A B σ₀ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ₀ A] [AddSubgroupClass σ₀ A]
  [SetLike τ B] [AddSubgroupClass τ B]
variable (𝒢 : ℕ → σ₀) (ℋ : ℕ → τ) [GradedRing 𝒢] [GradedRing ℋ]

set_option linter.style.haveILetI false in
theorem gradedRingHom_negativeToPositiveMul_stalk_eq_zero
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤
      (HomogeneousIdeal.irrelevant 𝒢).map f)
    {d : ℕ} (s : 𝒢 d) (m : ℕ) (hmd : m ≤ d)
    (hs : f s = 0)
    (y : ProjectiveSpectrum ℋ) :
    let x := ProjectiveSpectrum.comap f hf y
    ∀ z : stalkSubmodule 𝒢 x.asHomogeneousIdeal.toIdeal m,
      gradedRingHomPositiveTwistStalkMap 𝒢 ℋ f hf (d - m) y
        (negativeToPositiveMulHomogeneousStalk 𝒢
          x.asHomogeneousIdeal.toIdeal s m hmd z) = 0 := by
  dsimp only
  intro z
  let x := ProjectiveSpectrum.comap f hf y
  letI : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  letI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hxy : x.asHomogeneousIdeal.toIdeal =
      Ideal.comap f.toRingHom y.asHomogeneousIdeal.toIdeal := rfl
  apply Subtype.ext
  change Localization.localRingHom
      x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal f.toRingHom hxy
      (algebraMap A (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
        (s : A) * z.1) = 0
  rw [map_mul]
  have hs' : f.toRingHom (s : A) = 0 := hs
  have hsloc : Localization.localRingHom
      x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal f.toRingHom hxy
      (algebraMap A (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
        (s : A)) = 0 := by
    rw [← Localization.mk_one_eq_algebraMap,
      Localization.localRingHom_mk, hs', Localization.mk_zero]
  rw [hsloc, zero_mul]

end ProjectiveNegativeTwist
end PfaffianDescent
