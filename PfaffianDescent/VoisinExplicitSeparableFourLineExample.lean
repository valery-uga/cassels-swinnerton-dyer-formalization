import PfaffianDescent.VoisinStandardFourLineWitness
import AllCharacteristics.CubicLineAlgebra
import Mathlib.FieldTheory.Separable
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# An explicit transverse four-line cubic example

The diagonal cubic with coefficients `1,1,2,3` restricts to four polynomials
`T³+b` with nonzero constants on the standard four-line arrangement. This
gives a concrete separability witness for a future generic-parameter proof;
it does not assert transverse four-line sections for every smooth cubic.
-/

open PfaffianDescent MvPolynomial

namespace PfaffianDescent.VoisinExplicitSeparableFourLineExample

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def p₀ {K : Type*} [Field K] : MvPolynomial (Fin 4) K :=
  X 0 ^ 3 + X 1 ^ 3 + C (2 : K) * X 2 ^ 3 + C (3 : K) * X 3 ^ 3

theorem p₀_homogeneous {K : Type*} [Field K] :
    (p₀ (K := K)).IsHomogeneous 3 := by
  simp only [p₀]
  have h2 : ((C (2 : K) : MvPolynomial (Fin 4) K) * X 2 ^ 3).IsHomogeneous 3 := by
    change (C (2 : K) * X 2 ^ 3 : MvPolynomial (Fin 4) K) ∈ homogeneousSubmodule (Fin 4) K 3
    simpa only [MvPolynomial.smul_eq_C_mul] using
      (homogeneousSubmodule (Fin 4) K 3).smul_mem (2 : K)
        (isHomogeneous_X_pow (R := K) (2 : Fin 4) 3)
  have h3 : ((C (3 : K) : MvPolynomial (Fin 4) K) * X 3 ^ 3).IsHomogeneous 3 := by
    change (C (3 : K) * X 3 ^ 3 : MvPolynomial (Fin 4) K) ∈ homogeneousSubmodule (Fin 4) K 3
    simpa only [MvPolynomial.smul_eq_C_mul] using
      (homogeneousSubmodule (Fin 4) K 3).smul_mem (3 : K)
        (isHomogeneous_X_pow (R := K) (3 : Fin 4) 3)
  exact (((isHomogeneous_X_pow (R := K) (0 : Fin 4) 3).add
    (isHomogeneous_X_pow (R := K) (1 : Fin 4) 3)).add h2).add h3

theorem p₀_ne_zero {K : Type*} [Field K] : p₀ (K := K) ≠ 0 := by
  intro h
  have hv := congrArg (MvPolynomial.eval (Pi.single 0 (1 : K))) h
  simp [p₀, Pi.single_apply] at hv

def c₀ {K : Type*} [Field K] : Cubic K 4 :=
  Pi.single (0, 0, 0) 1 + Pi.single (1, 1, 1) 1 +
    Pi.single (2, 2, 2) 2 + Pi.single (3, 3, 3) 3

theorem c₀_eval {K : Type*} [Field K] (v : Fin 4 → K) :
    (c₀ (K := K)).eval v =
      v 0 ^ 3 + v 1 ^ 3 + 2 * v 2 ^ 3 + 3 * v 3 ^ 3 := by
  simp only [c₀, Cubic.eval, Pi.add_apply, Pi.single_apply]
  simp_rw [add_mul, Finset.sum_add_distrib]
  simp
  ring

theorem c₀_toMvPolynomial {K : Type*} [Field K] [CharZero K] :
    (c₀ (K := K)).toMvPolynomial = p₀ := by
  apply MvPolynomial.funext
  intro v
  have h := Cubic.eval_toMvPolynomial (RingHom.id K) (c₀ (K := K)) v
  change (c₀ (K := K)).toMvPolynomial.eval v = (c₀ (K := K)).eval v at h
  rw [c₀_eval] at h
  simpa [p₀] using h

def b₀ {K : Type*} [Field K] (i j : Fin 2) : K :=
  if i = 0 then (if j = 0 then 2 else -1)
  else (if j = 0 then 1 else -2)

theorem eval_line {K : Type*} [Field K] (i j : Fin 2) (t : K) :
    (p₀ (K := K)).eval (t • Pi.single 0 1 + lineDirection i j) =
      t ^ 3 + b₀ i j := by
  fin_cases i <;> fin_cases j
  all_goals simp [p₀, b₀, lineDirection, Pi.single, Pi.smul_apply,
    MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_pow] <;> ring

theorem b₀_ne_zero {K : Type*} [Field K] [CharZero K]
    (i j : Fin 2) : b₀ (K := K) i j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [b₀]

theorem linePolynomial_separable {K : Type*} [Field K] [CharZero K]
    (i j : Fin 2) :
    (Polynomial.X ^ 3 + Polynomial.C (b₀ (K := K) i j)).Separable := by
  have hn : (3 : K) ≠ 0 := by norm_num
  have hb : -(b₀ (K := K) i j) ≠ 0 := neg_ne_zero.mpr (b₀_ne_zero i j)
  convert Polynomial.separable_X_pow_sub_C
    (-(b₀ (K := K) i j)) hn hb using 1 <;> simp

theorem c₀_linePolynomial_eq {K : Type*} [Field K] [CharZero K]
    (i j : Fin 2) :
    AllCharacteristics.cubicLinePolynomial (c₀ (K := K))
      (Pi.single 0 1) (lineDirection i j) =
      Polynomial.X ^ 3 + Polynomial.C (b₀ (K := K) i j) := by
  apply Polynomial.funext
  intro t
  have h := AllCharacteristics.cubicLinePolynomial_eval₂
    (RingHom.id K) (c₀ (K := K)) (Pi.single 0 1) (lineDirection i j) t
  change (AllCharacteristics.cubicLinePolynomial (c₀ (K := K))
    (Pi.single 0 1) (lineDirection i j)).eval t =
    (c₀ (K := K)).eval (t • Pi.single 0 1 + lineDirection i j) at h
  have heval := eval_line (K := K) i j t
  rw [← c₀_toMvPolynomial] at heval
  have hc := Cubic.eval_toMvPolynomial (RingHom.id K) (c₀ (K := K))
    (t • Pi.single 0 1 + lineDirection i j)
  change (c₀ (K := K)).toMvPolynomial.eval
    (t • Pi.single 0 1 + lineDirection i j) =
    (c₀ (K := K)).eval (t • Pi.single 0 1 + lineDirection i j) at hc
  rw [hc] at heval
  simpa [heval] using h

theorem c₀_four_line_separable {K : Type*} [Field K] [CharZero K]
    (i j : Fin 2) :
    (AllCharacteristics.cubicLinePolynomial (c₀ (K := K))
      (Pi.single 0 1) (lineDirection i j)).Separable := by
  rw [c₀_linePolynomial_eq]
  exact linePolynomial_separable i j

theorem c₀_four_line_discr_ne_zero {K : Type*} [Field K] [CharZero K]
    (i j : Fin 2) :
    (AllCharacteristics.cubicLinePolynomial (c₀ (K := K))
      (Pi.single 0 1) (lineDirection i j)).discr ≠ 0 := by
  rw [c₀_linePolynomial_eq]
  have hdeg : (Polynomial.X ^ 3 + Polynomial.C (b₀ (K := K) i j)).degree = 3 := by
    exact Polynomial.degree_X_pow_add_C (by decide : 0 < 3) _
  rw [Polynomial.discr_of_degree_eq_three hdeg]
  simp only [Polynomial.coeff_add]
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_C_of_ne_zero]
  exact b₀_ne_zero i j

theorem c₀_base_ne_zero {K : Type*} [Field K] :
    (c₀ (K := K)).eval (Pi.single 0 1) ≠ 0 := by
  rw [c₀_eval]
  simpa [Pi.single_apply] using (one_ne_zero : (1 : K) ≠ 0)

end PfaffianDescent.VoisinExplicitSeparableFourLineExample
