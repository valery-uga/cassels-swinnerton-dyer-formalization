import PfaffianDescent.FrameMatrix
import PfaffianDescent.FrameDivisibility

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators

section
variable {K : Type*} [Field K]

/-- Exactness at the left free module of rank five in the frame resolution. -/
theorem frameMatrix_kernel (v : Fin 5 → MvPolynomial (Fin 4) K)
    (hv : (frameMatrix MvPolynomial.X).mulVec v = 0) :
    ∃ r : MvPolynomial (Fin 4) K, v = r • frameRelations (K := K) := by
  let x : Vec (MvPolynomial (Fin 4) K) 4 := MvPolynomial.X
  have h1 : x 1 * v 0 + x 2 * v 3 - x 1 * v 4 = 0 := by
    have h := congrFun hv 1
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change ((-(-x 1)) * v 0 + ((0) * v 1 + ((0) * v 2 + ((x 2) * v 3 + (-x 1) * v 4)))) = 0 at h
    linear_combination h
  have h2 : x 3 * v 0 + x 0 * v 3 - x 0 * v 4 = 0 := by
    have h := congrFun hv 2
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change ((-(-x 3)) * v 0 + ((0) * v 1 + ((0) * v 2 + ((x 0) * v 3 + (-x 0) * v 4)))) = 0 at h
    linear_combination h
  have h3 : -x 2 * v 1 - x 0 * v 2 + x 0 * v 4 = 0 := by
    have h := congrFun hv 3
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change ((0) * v 0 + ((-x 2) * v 1 + ((-x 0) * v 2 + ((0) * v 3 + (x 0) * v 4)))) = 0 at h
    linear_combination h
  have h4 : -x 1 * v 0 + x 1 * v 1 + x 0 * v 2 - x 0 * v 3 = 0 := by
    have h := congrFun hv 4
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
    change ((-x 1) * v 0 + ((-(-x 1)) * v 1 + ((-(-x 0)) * v 2 + ((-x 0) * v 3 + (0) * v 4)))) = 0 at h
    linear_combination h
  have hp : Prime (x 0) := MvPolynomial.X_prime
  have hx0 : x 0 ≠ 0 := hp.ne_zero
  have hva : x 0 ∣ v 0 := by
    have h : x 0 ∣ x 3 * v 0 := ⟨v 4 - v 3, by linear_combination h2⟩
    exact (hp.dvd_mul.mp h).resolve_left frame_X_zero_not_dvd_X_three
  have hvb : x 0 ∣ v 1 := by
    have h : x 0 ∣ x 2 * v 1 := ⟨v 4 - v 2, by linear_combination -h3⟩
    exact (hp.dvd_mul.mp h).resolve_left frame_X_zero_not_dvd_X_two
  obtain ⟨a, ha⟩ := hva
  obtain ⟨b, hb⟩ := hvb
  have he : v 4 = v 3 + x 3 * a := by
    apply mul_left_cancel₀ hx0
    linear_combination -h2 + x 3 * ha
  have hc : v 2 = v 4 - x 2 * b := by
    apply mul_left_cancel₀ hx0
    linear_combination -h3 - x 2 * hb
  have hab : (x 3 - x 1) * a = (x 2 - x 1) * b := by
    apply mul_left_cancel₀ hx0
    have h := h4
    rw [ha, hb, hc, he] at h
    linear_combination h
  have hprime : Prime (x 2 - x 1) := frame_difference_prime
  have hadiv : x 2 - x 1 ∣ a := by
    have h : x 2 - x 1 ∣ (x 3 - x 1) * a := ⟨b, hab⟩
    exact (hprime.dvd_mul.mp h).resolve_left frame_difference_not_dvd_other
  obtain ⟨r, har⟩ := hadiv
  have hbr : b = (x 3 - x 1) * r := by
    apply mul_left_cancel₀ hprime.ne_zero
    rw [har] at hab
    linear_combination -hab
  have hd : v 3 = x 1 * (x 3 - x 0) * r := by
    apply mul_left_cancel₀ hprime.ne_zero
    have h := h1
    rw [ha, he, har] at h
    linear_combination h
  refine ⟨r, ?_⟩
  funext i
  fin_cases i
  · change v 0 = r * (x 0*x 2-x 0*x 1)
    rw [ha, har]
    ring
  · change v 1 = r * (x 0*x 3-x 0*x 1)
    rw [hb, hbr]
    ring
  · change v 2 = r * (x 1*x 2-x 0*x 1)
    rw [hc, he, hd, har, hbr]
    ring
  · change v 3 = r * (x 1*x 3-x 0*x 1)
    rw [hd]
    ring
  · change v 4 = r * (x 2*x 3-x 0*x 1)
    rw [he, hd, har]
    ring

end
end PfaffianDescent
