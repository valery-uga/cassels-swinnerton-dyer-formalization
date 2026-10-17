import PfaffianDescent.QuadraticSkewLineSecantCoordinates
import Mathlib.Tactic

/-! SOURCE ONLY / UNVERIFIED. Exact rational-function inverse parameter
identities and reconstruction for the actual mixed-cubic secant formula.
No scheme-map, birationality, or rationality certificate is an input. -/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.SecondComposite005
open scoped Matrix
universe u
variable {L : Type u} [Field L]

def inverseT (α β : L) (v : Fin 4 → L) : L :=
  (α - β)⁻¹ * (α * v 3 * v 0 - β * v 1 * v 2) / (v 0 * v 2)

def inverseU (α β : L) (v : Fin 4 → L) : L :=
  (α - β)⁻¹ * (v 1 * v 2 - v 3 * v 0) / (v 0 * v 2)

theorem inverseT_add_left_mul_inverseU
    (α β : L) (hαβ : α ≠ β) (v : Fin 4 → L)
    (hv₀ : v 0 ≠ 0) (hv₂ : v 2 ≠ 0) :
    inverseT α β v + α * inverseU α β v = v 1 / v 0 := by
  unfold inverseT inverseU
  field_simp [sub_ne_zero.mpr hαβ, hv₀, hv₂]
  <;> ring

theorem inverseT_add_right_mul_inverseU
    (α β : L) (hαβ : α ≠ β) (v : Fin 4 → L)
    (hv₀ : v 0 ≠ 0) (hv₂ : v 2 ≠ 0) :
    inverseT α β v + β * inverseU α β v = v 3 / v 2 := by
  unfold inverseT inverseU
  field_simp [sub_ne_zero.mpr hαβ, hv₀, hv₂]
  <;> ring

/-- The recovered conjugate parameters reconstruct the entire split
coordinate vector, rather than only its affine parameter pair. -/
theorem residualCoordinates_at_inverseParameters
    (c : SplitMixedCubicCoefficients L) (α β : L) (hαβ : α ≠ β)
    (v : Fin 4 → L) (hv₀ : v 0 ≠ 0) (hv₂ : v 2 ≠ 0)
    (hFc : splitCubicValue c (v 0) (v 1) (v 2) (v 3) = 0) :
    residualCoordinates c
        (inverseT α β v + α * inverseU α β v)
        (inverseT α β v + β * inverseU α β v) =
      (rightMixedValue c 1 (v 1 / v 0) 1 (v 3 / v 2) / v 0) • v := by
  rw [inverseT_add_left_mul_inverseU α β hαβ v hv₀ hv₂,
    inverseT_add_right_mul_inverseU α β hαβ v hv₀ hv₂]
  have hvec : ![v 0, v 1, v 2, v 3] = v := by
    ext i
    fin_cases i <;> simp
  simpa only [hvec] using residualCoordinates_recover_point c
    (v 0) (v 1) (v 2) (v 3) hv₀ hv₂ hFc

theorem reconstruction_scalar_ne_zero
    (δ B x₀ : L) (hδ : δ ≠ 0) (hB : B ≠ 0) (hx₀ : x₀ ≠ 0) :
    δ * (B / x₀) ≠ 0 :=
  mul_ne_zero hδ (div_ne_zero hB hx₀)

end PfaffianDescent.QuadraticSkewRationality.SecondComposite005
