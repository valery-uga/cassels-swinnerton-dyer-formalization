import PfaffianDescent.HomogeneousChartVanishing
import PfaffianDescent.ProjectivePositiveTwist
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Pointwise vanishing on a projective chart

This is the bridge from zero fractions at all projective points to ordinary
localization at a homogeneous chart coordinate.
-/

namespace PfaffianDescent

open AlgebraicGeometry HomogeneousLocalization CategoryTheory
open ProjectiveNegativeTwist

universe u

theorem localization_eq_zero_of_projective_pointwise_zero
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]
    {s : A} (hs : s ∈ 𝒜 1) (n : ℕ) (a : A) (ha : a ∈ 𝒜 n)
    (hzero : ∀ x : ProjectiveSpectrum.top 𝒜,
      (Localization.mk a 1 : PositiveFiber 𝒜 x) = 0) :
    algebraMap A (Localization (Submonoid.powers s)) a = 0 := by
  let b := Away.mk 𝒜 hs n a (by simpa using ha)
  have hb : b = 0 := by
    let f := ProjectiveSpectrum.Proj.awayToSection 𝒜 s
    have hpoint (p : AlgebraicGeometry.Proj.basicOpen 𝒜 s) :
        (((f b).val p).val) = 0 := by
      change (((ProjectiveSpectrum.Proj.awayToSection 𝒜 s) b).val p).val = 0
      have hh := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 s b p
      exact hh.trans (by
        dsimp only [b]
        rw [Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
        apply (IsLocalization.mk'_eq_zero_iff _ _).mpr
        have hpzero : algebraMap A (PositiveFiber 𝒜 p.1) a = 0 := by
          simpa only [Localization.mk_one_eq_algebraMap] using hzero p.1
        exact (IsLocalization.map_eq_zero_iff _ _ _).mp hpzero)
    have hsec : f b = 0 := by
      apply Subtype.ext
      funext p
      apply (HomogeneousLocalization.ext_iff_val _ _).mpr
      simpa using hpoint p
    have hf : Function.Injective f := by
      intro x y hxy
      let E := AlgebraicGeometry.Proj.basicOpenIsoAway 𝒜 s hs (by decide)
      have h := congrArg (fun z => E.inv z) hxy
      have hcancel (z : Away 𝒜 s) : E.inv (f z) = z := by
        change (E.hom ≫ E.inv) z = z
        rw [E.hom_inv_id]
        rfl
      simpa only [hcancel] using h
    exact hf (by simpa only [map_zero] using hsec)
  exact localization_eq_zero_of_away_mk_eq_zero 𝒜 hs n a ha hb

end PfaffianDescent
