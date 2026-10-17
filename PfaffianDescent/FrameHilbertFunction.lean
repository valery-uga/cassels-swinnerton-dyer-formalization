import PfaffianDescent.FrameGrading
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace PfaffianDescent.FrameCoordinateRing
open Module Polynomial
open scoped BigOperators

section
variable {K : Type*} [Field K]

/-- Evaluation at the chosen representatives of the projective frame. -/
noncomputable def atPoint (p : Option (Fin 4)) : FrameCoordinateRing K →ₐ[K] K :=
  (Polynomial.aeval (1 : K)).comp (atLine p)

theorem atAxis_x (j i : Fin 4) : atPoint (K := K) (some j) (x i) =
    if i = j then 1 else 0 := by
  classical
  by_cases h : i = j <;> simp [atPoint, atLine_x, frameLineVariable, h]

theorem atDiagonal_x (i : Fin 4) : atPoint (K := K) none (x i) = 1 := by
  simp only [atPoint, AlgHom.comp_apply, atLine_x, frameLineVariable, aeval_X]

theorem atAxis_q (j : Fin 4) : atPoint (K := K) (some j) q = 0 := by
  simp only [atPoint, AlgHom.comp_apply, atLine_q, reduceCtorEq, ↓reduceIte, map_zero]

theorem atDiagonal_q : atPoint (K := K) none q = 1 := by
  simp only [atPoint, AlgHom.comp_apply, atLine_q, ↓reduceIte, map_pow, aeval_X, one_pow]

theorem atAxis_highGenerator (n : ℕ) (j : Fin 4) (p : Option (Fin 4)) :
    atPoint (K := K) (some j) (highGenerator n p) = if p = some j then 1 else 0 := by
  cases p with
  | none =>
      simp only [highGenerator, map_mul, atAxis_q, zero_mul, reduceCtorEq, ↓reduceIte]
  | some i =>
      rw [highGenerator, map_pow, atAxis_x]
      by_cases h : i = j
      · simp only [h, ↓reduceIte, one_pow]
      · simp only [h, ↓reduceIte, zero_pow (by omega : n+2 ≠ 0), Option.some.injEq]

theorem atDiagonal_highGenerator (n : ℕ) (p : Option (Fin 4)) :
    atPoint (K := K) none (highGenerator n p) = 1 := by
  cases p with
  | none => simp only [highGenerator, map_mul, map_pow, atDiagonal_q, atDiagonal_x, one_pow, mul_one]
  | some i => simp only [highGenerator, map_pow, atDiagonal_x, one_pow]

theorem variables_independent : LinearIndependent K (x (K := K)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have h := congrArg (atPoint (K := K) (some j)) hc
  simp only [map_sum, map_smul, map_zero, atAxis_x, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
  exact h

/-- Evaluation on the frame proves the five spanning classes independent. -/
theorem highGenerators_independent (n : ℕ) :
    LinearIndependent K (highGenerator (K := K) n) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have hs (j : Fin 4) : c (some j) = 0 := by
    have h := congrArg (atPoint (K := K) (some j)) hc
    simp only [map_sum, map_smul, map_zero, atAxis_highGenerator, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
    exact h
  cases p with
  | some j => exact hs j
  | none =>
      have h := congrArg (atPoint (K := K) none) hc
      simp only [map_sum, map_smul, map_zero, atDiagonal_highGenerator, smul_eq_mul,
        mul_one, Fintype.sum_option, hs, zero_smul, Finset.sum_const_zero, add_zero] at h
      exact h

theorem hilbert_zero : finrank K (component (K := K) 0) = 1 := by
  rw [component_pow, Submodule.pow_zero, Submodule.one_eq_span]
  apply finrank_span_singleton
  intro h
  have he := congrArg (atPoint (K := K) none) h
  exact one_ne_zero (by simpa only [map_one, map_zero] using he)

theorem hilbert_one : finrank K (component (K := K) 1) = 4 := by
  rw [component_one, finrank_span_eq_card variables_independent]
  rfl

/-- The homogeneous coordinate ring has Hilbert function `1,4,5,5,5,…`. -/
theorem hilbert_high (n : ℕ) : finrank K (component (K := K) (n+2)) = 5 := by
  rw [component_high, highSpan, finrank_span_eq_card (highGenerators_independent n)]
  rfl

end
end PfaffianDescent.FrameCoordinateRing
