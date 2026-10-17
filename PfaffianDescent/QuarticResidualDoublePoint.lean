import PfaffianDescent.QuarticInfinitesimalPoints

/-!
# Residual roots from quartic double points

The degree-nine residual argument used by the exceptional twisted-cubic
branch of Section 4.  A separable quartic double point accounts for eight
roots, leaving a rational residual root.
-/

namespace PfaffianDescent
namespace QuarticNet

open Polynomial TrivSqZeroExt

universe u

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

theorem minpoly_square_dvd_of_double_root [Algebra.IsSeparable k L]
    (a : L) (P : k[X]) (hP : aeval a P = 0) (hd : aeval a P.derivative = 0) :
    minpoly k a ^ 2 ∣ P := by
  obtain ⟨Q, hQ⟩ := minpoly.dvd k a hP
  have hm := minpoly.aeval k a
  have hmd := (Algebra.IsSeparable.isSeparable k a).aeval_derivative_ne_zero hm
  have hQroot : aeval a Q = 0 := by
    rw [hQ, derivative_mul, map_add, map_mul, map_mul, hm, zero_mul, add_zero] at hd
    exact (mul_eq_zero.mp hd).resolve_left hmd
  obtain ⟨R, hR⟩ := minpoly.dvd k a hQroot
  exact ⟨R, by rw [hQ, hR, pow_two, mul_assoc]⟩

theorem minpoly_square_dvd_of_dual_zero [Algebra.IsSeparable k L]
    (a b : L) (hb : b ≠ 0) (P : k[X])
    (hP : aeval (inl a + inr b : DualNumber L) P = 0) : minpoly k a ^ 2 ∣ P := by
  have h0 := congrArg TrivSqZeroExt.fst hP
  have h1 := congrArg TrivSqZeroExt.snd hP
  rw [polynomial_aeval_dual] at h0 h1
  simp only [fst_add, fst_inl, fst_inr, add_zero, fst_zero] at h0
  simp only [snd_add, snd_inl, snd_inr, zero_add, snd_zero] at h1
  exact minpoly_square_dvd_of_double_root a P h0
    ((mul_eq_zero.mp h1).resolve_right hb)

theorem polynomial_root_of_residual_degree_one (P Q : k[X])
    (hP : P.natDegree = Q.natDegree + 1) (hdiv : Q ∣ P) :
    ∃ r : k, P.IsRoot r := by
  obtain ⟨R, hR⟩ := hdiv
  have hPn : P ≠ 0 := by
    intro h
    simp [h] at hP
  have hn : Q ≠ 0 ∧ R ≠ 0 := by
    exact ⟨fun h => hPn (by simp [hR, h]), fun h => hPn (by simp [hR, h])⟩
  have hdeg : R.natDegree = 1 := by
    have h := congrArg Polynomial.natDegree hR
    rw [hP, natDegree_mul hn.1 hn.2] at h
    omega
  obtain ⟨r, hr⟩ := exists_root_of_degree_eq_one
    ((degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 1)).mpr hdeg)
  refine ⟨r, ?_⟩
  change eval r P = 0
  change eval r R = 0 at hr
  rw [hR, eval_mul, hr, mul_zero]

/-- A degree-nine polynomial containing the length-eight double point at a
separable quartic element has a rational residual root. -/
theorem degree_nine_root_of_quartic_double_point [Algebra.IsSeparable k L]
    (a b : L) (hb : b ≠ 0) (ha : (minpoly k a).natDegree = 4)
    (P : k[X]) (hdeg : P.natDegree = 9)
    (hP : aeval (inl a + inr b : DualNumber L) P = 0) :
    ∃ r : k, P.IsRoot r := by
  apply polynomial_root_of_residual_degree_one P (minpoly k a ^ 2)
  · simp only [hdeg, natDegree_pow, ha]
  · exact minpoly_square_dvd_of_dual_zero a b hb P hP

end QuarticNet
end PfaffianDescent
