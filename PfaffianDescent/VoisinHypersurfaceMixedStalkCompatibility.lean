import PfaffianDescent.ProjectivePositiveDifferencePairing
import PfaffianDescent.VoisinHypersurfacePositiveTwist

/-!
# Compatibility of mixed twist products with hypersurface quotient stalks
-/

noncomputable section

namespace PfaffianDescent

open scoped DirectSum Pointwise TensorProduct
open DirectSum SetLike Localization
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

namespace ProjectiveNegativeTwist

variable {A B σ₀ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ₀ A] [AddSubgroupClass σ₀ A]
  [SetLike τ B] [AddSubgroupClass τ B]
variable (𝒢 : ℕ → σ₀) (ℋ : ℕ → τ) [GradedRing 𝒢] [GradedRing ℋ]

set_option linter.style.haveILetI false in
/-- A graded map commutes with the positive-result mixed product on concrete
homogeneous-fraction stalks. -/
theorem gradedRingHomPositiveNegativePositiveDifferenceStalk_compat_of_le
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤
      (HomogeneousIdeal.irrelevant 𝒢).map f)
    (y : ProjectiveSpectrum ℋ)
    (m n : ℕ) (hnm : n ≤ m)
    (a : let x := ProjectiveSpectrum.comap f hf y
      positiveStalkSubmodule 𝒢 x.asHomogeneousIdeal.toIdeal m)
    (b : let x := ProjectiveSpectrum.comap f hf y
      stalkSubmodule 𝒢 x.asHomogeneousIdeal.toIdeal n) :
    let x := ProjectiveSpectrum.comap f hf y
    ((gradedRingHomPositiveTwistStalkMap 𝒢 ℋ f hf m y a).1) *
      ((gradedRingHomTwistStalkMap 𝒢 ℋ f hf n y b).1) =
    (gradedRingHomPositiveTwistStalkMap 𝒢 ℋ f hf (m - n) y
      (positiveNegativePositiveDifferenceStalkBilinear 𝒢
        x.asHomogeneousIdeal.toIdeal m n hnm a b)).1 := by
  dsimp [gradedRingHomPositiveTwistStalkMap,
    gradedRingHomTwistStalkMap,
    positiveNegativePositiveDifferenceStalkBilinear]
  let x := ProjectiveSpectrum.comap f hf y
  letI : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  letI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hxy : x.asHomogeneousIdeal.toIdeal =
      Ideal.comap f.toRingHom y.asHomogeneousIdeal.toIdeal := rfl
  change Localization.localRingHom
      x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal f.toRingHom hxy a.1 *
      Localization.localRingHom
        x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal f.toRingHom hxy b.1 =
    Localization.localRingHom
      x.asHomogeneousIdeal.toIdeal y.asHomogeneousIdeal.toIdeal f.toRingHom hxy
      (a.1 * b.1)
  exact (map_mul _ _ _).symm

/-- The `(5,3)` specialization used for the positively twisted cubic
restriction sequence. -/
theorem gradedRingHomPositiveNegativePositiveDifferenceStalk_compat
    (f : 𝒢 →+*ᵍ ℋ)
    (hf : HomogeneousIdeal.irrelevant ℋ ≤
      (HomogeneousIdeal.irrelevant 𝒢).map f)
    (y : ProjectiveSpectrum ℋ)
    (a : let x := ProjectiveSpectrum.comap f hf y
      positiveStalkSubmodule 𝒢 x.asHomogeneousIdeal.toIdeal 5)
    (b : let x := ProjectiveSpectrum.comap f hf y
      stalkSubmodule 𝒢 x.asHomogeneousIdeal.toIdeal 3) :
    let x := ProjectiveSpectrum.comap f hf y
    ((gradedRingHomPositiveTwistStalkMap 𝒢 ℋ f hf 5 y a).1) *
      ((gradedRingHomTwistStalkMap 𝒢 ℋ f hf 3 y b).1) =
    (gradedRingHomPositiveTwistStalkMap 𝒢 ℋ f hf 2 y
      (positiveNegativePositiveDifferenceStalkBilinear 𝒢
        x.asHomogeneousIdeal.toIdeal 5 3 (by omega) a b)).1 := by
  exact gradedRingHomPositiveNegativePositiveDifferenceStalk_compat_of_le
    𝒢 ℋ f hf y 5 3 (by omega) a b

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} {σ : Type} [Field K]
local notation "𝒜" => MvPolynomial.homogeneousSubmodule σ K

/-- For the projective hypersurface quotient, restricting the two factors
and multiplying on the hypersurface agrees with ambient multiplication
followed by restriction. -/
theorem hypersurfacePositiveNegativePositiveDifferenceStalk_compat
    (p : MvPolynomial σ K) {d : ℕ} (hp : p.IsHomogeneous d)
    (y : ProjectiveSpectrum (grading (equationIdeal p hp)))
    (a : let I := equationIdeal p hp
      let q := quotientGradedRingHom I
      let x := ProjectiveSpectrum.comap q
        (irrelevant_le_map_quotientGradedRingHom I) y
      positiveStalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal 5)
    (b : let I := equationIdeal p hp
      let q := quotientGradedRingHom I
      let x := ProjectiveSpectrum.comap q
        (irrelevant_le_map_quotientGradedRingHom I) y
      stalkSubmodule 𝒜 x.asHomogeneousIdeal.toIdeal 3) :
    let I := equationIdeal p hp
    let q := quotientGradedRingHom I
    let x := ProjectiveSpectrum.comap q
      (irrelevant_le_map_quotientGradedRingHom I) y
    positiveNegativePositiveDifferenceStalkBilinear
      (grading (equationIdeal p hp)) y.asHomogeneousIdeal.toIdeal 5 3 (by omega)
      (hypersurfacePositiveTwistStalkMap p hp 5 y a)
      (hypersurfaceTwistStalkMap p hp 3 y b) =
    hypersurfacePositiveTwistStalkMap p hp 2 y
      (positiveNegativePositiveDifferenceStalkBilinear 𝒜
        x.asHomogeneousIdeal.toIdeal 5 3 (by omega) a b) := by
  apply Subtype.ext
  exact gradedRingHomPositiveNegativePositiveDifferenceStalk_compat
    𝒜 (grading (equationIdeal p hp))
    (quotientGradedRingHom (equationIdeal p hp))
    (irrelevant_le_map_quotientGradedRingHom (equationIdeal p hp)) y a b

end ProjectiveNegativeTwist
end PfaffianDescent
