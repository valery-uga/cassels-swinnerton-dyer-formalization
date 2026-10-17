import PfaffianDescent.HomogeneousChartLength

/-!
# From projective-chart vanishing to ordinary localization

The degree-zero homogeneous localization used by `Proj` records a normalized
homogeneous equation.  If that normalized equation vanishes, the original
homogeneous element vanishes after ordinary localization at the chart
coordinate.
-/

namespace PfaffianDescent

open HomogeneousLocalization

section

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜] {z : A} (hz : z ∈ 𝒜 1)

/-- Vanishing of the normalized degree-`n` fraction in a homogeneous affine
chart implies vanishing of its numerator after localizing at the denominator.
-/
theorem localization_eq_zero_of_away_mk_eq_zero
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 n)
    (hzero : Away.mk 𝒜 hz n a (by simpa using ha) = 0) :
    algebraMap A (Localization (Submonoid.powers z)) a = 0 := by
  let b := Away.mk 𝒜 hz n a (by simpa using ha)
  have hbEq : b = 0 := by
    simpa only [b] using hzero
  have hb : b.val = 0 := by
    simpa using congrArg (fun c : Away 𝒜 z => c.val) hbEq
  have he : algebraMap A (Localization (Submonoid.powers z)) (z^n) * b.val =
      algebraMap A (Localization (Submonoid.powers z)) a := by
    rw [← Algebra.smul_def]
    change z^n • (Away.mk 𝒜 hz n a _).val = _
    rw [Away.val_mk, Localization.mk_eq_mk']
    exact IsLocalization.smul_mk'_self (M := Submonoid.powers z)
      (S := Localization (Submonoid.powers z))
      (m := ⟨z^n, ⟨n, rfl⟩⟩) (r := a)
  rw [hb, mul_zero] at he
  exact he.symm

end

end PfaffianDescent
