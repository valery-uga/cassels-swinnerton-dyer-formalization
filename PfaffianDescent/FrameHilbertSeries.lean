import PfaffianDescent.FrameHilbertFunction
import Mathlib.RingTheory.PowerSeries.WellKnown

namespace PfaffianDescent.FrameCoordinateRing
open Module PowerSeries

section
variable (K : Type*) [Field K]

/-- The Hilbert series formed from the dimensions of the actual homogeneous quotient. -/
noncomputable def hilbertSeries : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (finrank K (component (K := K) n) : ℤ))

theorem hilbertSeries_denominator :
    hilbertSeries K * (1 - X) = 1 + 3 * X + X ^ 2 := by
  have hthree : (3 : PowerSeries ℤ) = C 3 := (map_ofNat C 3).symm
  have hconstant : constantCoeff (3 : PowerSeries ℤ) = 3 := by rw [hthree, constantCoeff_C]
  have hcoeff (n : ℕ) : coeff n (3 : PowerSeries ℤ) = if n = 0 then 3 else 0 := by
    rw [hthree, coeff_C]
  rw [mul_sub, mul_one]
  apply PowerSeries.ext
  intro n
  rcases n with _ | n
  · simp [hilbertSeries, hilbert_zero, coeff_zero_mul_X]
  · rw [map_sub, coeff_succ_mul_X]
    rcases n with _ | n
    · norm_num [hconstant, hcoeff, hilbertSeries, hilbert_zero, hilbert_one, map_add, coeff_one,
        coeff_X_pow, coeff_succ_mul_X]
    · rcases n with _ | n
      · norm_num [hconstant, hcoeff, hilbertSeries, hilbert_one, hilbert_high, map_add, coeff_one,
          coeff_X_pow, coeff_succ_mul_X]
      · have h0 : n+1+1+1 ≠ 0 := by omega
        have h1 : n+1+1+1 ≠ 1 := by omega
        have h2 : n+1+1+1 ≠ 2 := by omega
        simp only [hilbertSeries, coeff_mk, hilbert_high, map_add, coeff_one,
          h0, ↓reduceIte, coeff_succ_mul_X, coeff_X_pow, h2]
        norm_num [hcoeff]

/-- The rational expression `(1+3X+X²)/(1-X)`, using the geometric series inverse. -/
theorem hilbertSeries_formula :
    hilbertSeries K = (1 + 3 * X + X ^ 2) * (PowerSeries.mk (fun _ => (1 : ℤ))) := by
  have hinv : ((1 : PowerSeries ℤ) - X) * PowerSeries.mk (fun _ => (1 : ℤ)) = 1 := by
    rw [mul_comm]
    exact PowerSeries.mk_one_mul_one_sub_eq_one ℤ
  calc
    hilbertSeries K = hilbertSeries K * ((1-X) * PowerSeries.mk (fun _ => (1 : ℤ))) := by rw [hinv, mul_one]
    _ = (hilbertSeries K * (1-X)) * PowerSeries.mk (fun _ => (1 : ℤ)) := by ring
    _ = _ := by rw [hilbertSeries_denominator]

/-- The polynomial numerator predicting the shifts in the five-point resolution. -/
theorem hilbert_resolution_numerator :
    (1 + 3 * (X : PowerSeries ℤ) + X ^ 2) * (1-X) ^ 3 =
      1 - 5 * X ^ 2 + 5 * X ^ 3 - X ^ 5 := by ring

end
end PfaffianDescent.FrameCoordinateRing
