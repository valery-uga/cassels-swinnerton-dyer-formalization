import PfaffianDescent.QuarticTwistedCubicVeronese
import PfaffianDescent.HomogeneousIdealPieces

/-!
# The quadratic piece of the standard twisted-cubic ideal

The three Hankel quadrics are linearly independent.  Together with the
generic homogeneous-ideal calculation, this identifies the quadratic piece
of the standard projective twisted cubic as a three-dimensional space.
-/

namespace PfaffianDescent.QuarticNet

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K]

set_option linter.unusedSimpArgs false in
/-- The three standard Hankel quadrics are linearly independent. -/
theorem standardTwistedCubicGenerators_linearIndependent :
    LinearIndependent K (standardTwistedCubicGenerators K) := by
  have hXmul (i j : Fin 4) : X i * X j =
      monomial (Finsupp.single i 1 + Finsupp.single j 1) (1 : K) := by
    change monomial (Finsupp.single i 1) (1 : K) * monomial (Finsupp.single j 1) 1 = _
    rw [monomial_mul, mul_one]
  let e0 : Fin 4 →₀ ℕ := Finsupp.single 1 2
  let e1 : Fin 4 →₀ ℕ := Finsupp.single 1 1 + Finsupp.single 2 1
  let e2 : Fin 4 →₀ ℕ := Finsupp.single 2 2
  have finsupp_ne (a b : Fin 4 →₀ ℕ) (i : Fin 4) (h : a i ≠ b i) : a ≠ b := by
    intro hab
    exact h (DFunLike.congr_fun hab i)
  have h_a0 : Finsupp.single (0 : Fin 4) 1 + Finsupp.single 2 1 ≠ e0 :=
    finsupp_ne _ _ 0 (by simp [e0, e1, e2])
  have h_b0 : Finsupp.single (1 : Fin 4) 1 + Finsupp.single 2 1 ≠ e0 :=
    finsupp_ne _ _ 1 (by simp [e0, e1, e2])
  have h_c0 : Finsupp.single (0 : Fin 4) 1 + Finsupp.single 3 1 ≠ e0 :=
    finsupp_ne _ _ 0 (by simp [e0, e1, e2])
  have h_d0 : Finsupp.single (2 : Fin 4) 2 ≠ e0 :=
    finsupp_ne _ _ 1 (by simp [e0, e1, e2])
  have h_f0 : Finsupp.single (1 : Fin 4) 1 + Finsupp.single 3 1 ≠ e0 :=
    finsupp_ne _ _ 3 (by simp [e0, e1, e2])
  have h_0b : e0 ≠ e1 := finsupp_ne _ _ 1 (by simp [e0, e1, e2])
  have h_s01 : Finsupp.single (0 : Fin 4) 1 ≠ Finsupp.single 1 1 :=
    finsupp_ne _ _ 0 (by simp [e0, e1, e2])
  have h_cb : Finsupp.single (0 : Fin 4) 1 + Finsupp.single 3 1 ≠ e1 :=
    finsupp_ne _ _ 0 (by simp [e0, e1, e2])
  have h_db : Finsupp.single (2 : Fin 4) 2 ≠ e1 :=
    finsupp_ne _ _ 1 (by simp [e0, e1, e2])
  have h_s32 : Finsupp.single (3 : Fin 4) 1 ≠ Finsupp.single 2 1 :=
    finsupp_ne _ _ 3 (by simp [e0, e1, e2])
  have h_0d : e0 ≠ e2 := finsupp_ne _ _ 1 (by simp [e0, e1, e2])
  have h_ad : Finsupp.single (0 : Fin 4) 1 + Finsupp.single 2 1 ≠ e2 :=
    finsupp_ne _ _ 0 (by simp [e0, e1, e2])
  have h_bd : e1 ≠ e2 := finsupp_ne _ _ 1 (by simp [e0, e1, e2])
  have h_cd : Finsupp.single (0 : Fin 4) 1 + Finsupp.single 3 1 ≠ e2 :=
    finsupp_ne _ _ 0 (by simp [e0, e1, e2])
  have h_fd : Finsupp.single (1 : Fin 4) 1 + Finsupp.single 3 1 ≠ e2 :=
    finsupp_ne _ _ 3 (by simp [e0, e1, e2])
  have h_e0b : Finsupp.single (1 : Fin 4) 2 ≠
      Finsupp.single 1 1 + Finsupp.single 2 1 :=
    finsupp_ne _ _ 1 (by simp [e0, e1, e2])
  have h_e0d : Finsupp.single (1 : Fin 4) 2 ≠ Finsupp.single 2 2 :=
    finsupp_ne _ _ 1 (by simp [e0, e1, e2])
  have h_bd' : Finsupp.single (1 : Fin 4) 1 + Finsupp.single 2 1 ≠
      Finsupp.single 2 2 :=
    finsupp_ne _ _ 1 (by simp [e0, e1, e2])
  have h00 : coeff e0 (standardTwistedCubicGenerators K 0) = 1 := by
    simp [standardTwistedCubicGenerators, e0, X_pow_eq_monomial, hXmul, h_a0, h_b0, h_c0,
      h_d0, h_f0, h_0b, h_s01, h_cb, h_db, h_s32, h_0d, h_ad, h_bd, h_cd, h_fd,
      h_e0b, h_e0d, h_bd']
  have h01 : coeff e0 (standardTwistedCubicGenerators K 1) = 0 := by
    simp [standardTwistedCubicGenerators, e0, X_pow_eq_monomial, hXmul, h_a0, h_b0, h_c0,
      h_d0, h_f0, h_0b, h_s01, h_cb, h_db, h_s32, h_0d, h_ad, h_bd, h_cd, h_fd,
      h_e0b, h_e0d, h_bd']
  have h02 : coeff e0 (standardTwistedCubicGenerators K 2) = 0 := by
    simp [standardTwistedCubicGenerators, e0, X_pow_eq_monomial, hXmul, h_a0, h_b0, h_c0,
      h_d0, h_f0, h_0b, h_s01, h_cb, h_db, h_s32, h_0d, h_ad, h_bd, h_cd, h_fd,
      h_e0b, h_e0d, h_bd']
  have h10 : coeff e1 (standardTwistedCubicGenerators K 0) = 0 := by
    simp [standardTwistedCubicGenerators, e1, X_pow_eq_monomial, hXmul, h_a0, h_b0, h_c0,
      h_d0, h_f0, h_0b, h_s01, h_cb, h_db, h_s32, h_0d, h_ad, h_bd, h_cd, h_fd,
      h_e0b, h_e0d, h_bd']
  have h11 : coeff e1 (standardTwistedCubicGenerators K 1) = 1 := by
    simp [standardTwistedCubicGenerators, e1, X_pow_eq_monomial, hXmul, h_a0, h_b0, h_c0,
      h_d0, h_f0, h_0b, h_s01, h_cb, h_db, h_s32, h_0d, h_ad, h_bd, h_cd, h_fd,
      h_e0b, h_e0d, h_bd']
  have h12 : coeff e1 (standardTwistedCubicGenerators K 2) = 0 := by
    simp [standardTwistedCubicGenerators, e1, X_pow_eq_monomial, hXmul, h_a0, h_b0, h_c0,
      h_d0, h_f0, h_0b, h_s01, h_cb, h_db, h_s32, h_0d, h_ad, h_bd, h_cd, h_fd,
      h_e0b, h_e0d, h_bd']
  have h20 : coeff e2 (standardTwistedCubicGenerators K 0) = 0 := by
    simp [standardTwistedCubicGenerators, e2, X_pow_eq_monomial, hXmul, h_a0, h_b0, h_c0,
      h_d0, h_f0, h_0b, h_s01, h_cb, h_db, h_s32, h_0d, h_ad, h_bd, h_cd, h_fd,
      h_e0b, h_e0d, h_bd']
  have h21 : coeff e2 (standardTwistedCubicGenerators K 1) = 0 := by
    simp [standardTwistedCubicGenerators, e2, X_pow_eq_monomial, hXmul, h_a0, h_b0, h_c0,
      h_d0, h_f0, h_0b, h_s01, h_cb, h_db, h_s32, h_0d, h_ad, h_bd, h_cd, h_fd,
      h_e0b, h_e0d, h_bd']
  have h22 : coeff e2 (standardTwistedCubicGenerators K 2) = 1 := by
    simp [standardTwistedCubicGenerators, e2, X_pow_eq_monomial, hXmul, h_a0, h_b0, h_c0,
      h_d0, h_f0, h_0b, h_s01, h_cb, h_db, h_s32, h_0d, h_ad, h_bd, h_cd, h_fd,
      h_e0b, h_e0d, h_bd']
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  fin_cases i
  · have h := congrArg (coeff e0) hsum
    rw [Fin.sum_univ_succ] at h
    simpa [h00, h01, h02] using h
  · have h := congrArg (coeff e1) hsum
    rw [Fin.sum_univ_succ] at h
    simpa [h10, h11, h12] using h
  · have h := congrArg (coeff e2) hsum
    rw [Fin.sum_univ_succ] at h
    simpa [h20, h21, h22] using h

/-- The standard twisted-cubic ideal is generated by its quadratic piece. -/
theorem standardTwistedCubicHomogeneousIdeal_quadraticPieceGenerates :
    quadraticPieceGenerates (standardTwistedCubicHomogeneousIdeal (K := K)) := by
  apply quadraticPieceGenerates_of_ideal_eq_span_quadrics
    (standardTwistedCubicHomogeneousIdeal (K := K)) (standardTwistedCubicGenerators K)
  · exact standardTwistedCubicGenerators_homogeneous K
  · rfl

/-- The quadratic piece of the standard projective twisted cubic has dimension three. -/
theorem standardTwistedCubicHomogeneousIdeal_quadraticPiece_finrank :
    Module.finrank K (homogeneousIdealPiece (standardTwistedCubicHomogeneousIdeal (K := K)) 2) = 3 := by
  apply finrank_homogeneousIdealPiece_eq_three_of_ideal_eq_span_quadrics
    (standardTwistedCubicHomogeneousIdeal (K := K)) (standardTwistedCubicGenerators K)
  · exact standardTwistedCubicGenerators_homogeneous K
  · rfl
  · exact standardTwistedCubicGenerators_linearIndependent

end PfaffianDescent.QuarticNet
