import PfaffianDescent.QuinticSyzygyMatrix
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Tactic.LinearCombination

namespace PfaffianDescent
open scoped BigOperators
section
variable {R : Type*} [CommRing R] [IsDomain R]

/-- On the coordinate hyperplane `x₀ = 0`, elementary prime divisibility
identifies the full kernel of the quintic alternating matrix. -/
theorem quintic_boundary_kernel (a : Vec R 5) (y : Vec R 3)
    (hp : Prime (y 0)) (hn : ¬ y 0 ∣ y 1) (v : Vec R 5)
    (hv : (quinticSyzygyMatrix a ![0, y 0, y 1, y 2]).mulVec v = 0) :
    ∃ r : R, v = r • quinticQuadrics a ![0, y 0, y 1, y 2] := by
  have h4 : y 1 * v 0 = y 0 * v 1 := by
    have h := congrFun hv 4
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change -(y 1) * v 0 + (-(-y 0) * v 1 + (-(0) * v 2 + (-(0) * v 3 + 0 * v 4))) = 0 at h
    linear_combination -h
  have h3 : y 2 * v 0 - y 1 * v 1 + y 0 * v 2 = 0 := by
    have h := congrFun hv 3
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change -(-y 2) * v 0 + (-(y 1) * v 1 + (-(-y 0) * v 2 + (0 * v 3 + 0 * v 4))) = 0 at h
    linear_combination h
  have h2 : -(a 4 * y 2) * v 0 - y 2 * v 1 - y 0 * v 3 = 0 := by
    have h := congrFun hv 2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change -(a 4 * y 2 + a 1 * 0) * v 0 + (-(y 2 + a 2 * 0) * v 1 + (0 * v 2 + (-y 0 * v 3 + 0 * v 4))) = 0 at h
    linear_combination h
  have h1 : -(a 3 * y 2) * v 0 + y 2 * v 2 + y 1 * v 3 - y 0 * v 4 = 0 := by
    have h := congrFun hv 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change -(a 3 * y 2 + a 0 * 0) * v 0 + (0 * v 1 + ((y 2 + a 2 * 0) * v 2 + (y 1 * v 3 + -y 0 * v 4))) = 0 at h
    linear_combination h
  have hd0 : y 0 ∣ v 0 := (hp.dvd_mul.mp ⟨v 1, h4⟩).resolve_left hn
  obtain ⟨b, hb⟩ := hd0
  have hv1 : v 1 = y 1 * b := by
    apply mul_left_cancel₀ hp.ne_zero
    linear_combination -h4 + y 1 * hb
  have hdb : y 0 ∣ b := by
    have hd : y 0 ∣ y 1^2 * b := ⟨y 2 * b + v 2, by
      rw [hb, hv1] at h3
      linear_combination -h3⟩
    exact (hp.dvd_mul.mp hd).resolve_left (fun h => hn (hp.dvd_of_dvd_pow h))
  obtain ⟨r, hr⟩ := hdb
  have hv2 : v 2 = (y 1^2 - y 0 * y 2) * r := by
    apply mul_left_cancel₀ hp.ne_zero
    rw [hb, hv1, hr] at h3
    linear_combination h3
  have hv3 : v 3 = -(y 1 * y 2 + a 4 * y 0 * y 2) * r := by
    apply mul_left_cancel₀ hp.ne_zero
    rw [hb, hv1, hr] at h2
    linear_combination -h2
  have hv4 : v 4 = -(y 2^2 + a 4 * y 1 * y 2 + a 3 * y 0 * y 2) * r := by
    apply mul_left_cancel₀ hp.ne_zero
    rw [hb, hr, hv2, hv3] at h1
    linear_combination -h1
  refine ⟨-r, ?_⟩
  funext i
  fin_cases i
  · change v 0 = -r * (0 * y 1 - y 0^2)
    rw [hb, hr]
    ring
  · change v 1 = -r * (0 * y 2 - y 0 * y 1)
    rw [hv1, hr]
    ring
  · change v 2 = -r * (y 0 * y 2 - y 1^2)
    rw [hv2]
    ring
  · change v 3 = -r * (y 1 * y 2 + a 4 * y 0 * y 2 + a 3 * 0 * y 2 + a 2 * 0 * y 1 + a 1 * 0 * y 0 + a 0 * 0^2)
    rw [hv3]
    ring
  · change v 4 = -r * (y 2^2 + a 4 * y 1 * y 2 + a 3 * y 0 * y 2 + a 2 * 0 * y 2 + a 1 * 0 * y 1 + a 0 * 0 * y 0)
    rw [hv4]
    ring

end
end PfaffianDescent
