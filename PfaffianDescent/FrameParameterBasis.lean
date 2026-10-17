import PfaffianDescent.FrameParameterSpan
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.LinearAlgebra.Dimension.Free

namespace PfaffianDescent.FrameCoordinateRing
open Polynomial Module
open scoped BigOperators
section
variable {K : Type*} [Field K]

lemma atAxis_parameter_smul (j : Fin 4) (p : K[X]) (a : FrameCoordinateRing K) :
    atLine (some j) (p • a) = p * atLine (some j) a := by
  rw [parameter_smul, map_mul, ← aeval_algHom_apply, atAxis_ell, aeval_X_left_apply]

lemma atDiagonal_parameter_smul (p : K[X]) (a : FrameCoordinateRing K) :
    atLine none (p • a) = aeval (4 * X) p * atLine none a := by
  rw [parameter_smul, map_mul, ← aeval_algHom_apply, atDiagonal_ell]

/-- The five parameter generators are linearly independent over the polynomial ring. -/
theorem parameterGenerators_independent [CharZero K] :
    LinearIndependent K[X] (parameterGenerators (K := K)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have ha (j : Fin 4) : ∑ k, c k * atLine (some j) (parameterGenerators (K := K) k) = 0 := by
    have h := congrArg (atLine (K := K) (some j)) hc
    simpa only [map_sum, atAxis_parameter_smul, map_zero] using h
  have h0 : c 0 = 0 := by
    simpa [parameterGenerators, Fin.sum_univ_succ, atLine_x, atLine_q, frameLineVariable] using ha 3
  have h1 : c 1 = 0 := by
    have h : c 1 * X = 0 := by
      simpa [parameterGenerators, Fin.sum_univ_succ, atLine_x, atLine_q, frameLineVariable, h0]
        using ha 0
    exact (mul_eq_zero.mp h).resolve_right X_ne_zero
  have h2 : c 2 = 0 := by
    have h : c 2 * X = 0 := by
      simpa [parameterGenerators, Fin.sum_univ_succ, atLine_x, atLine_q, frameLineVariable, h0]
        using ha 1
    exact (mul_eq_zero.mp h).resolve_right X_ne_zero
  have h3 : c 3 = 0 := by
    have h : c 3 * X = 0 := by
      simpa [parameterGenerators, Fin.sum_univ_succ, atLine_x, atLine_q, frameLineVariable, h0]
        using ha 2
    exact (mul_eq_zero.mp h).resolve_right X_ne_zero
  have h4 : c 4 = 0 := by
    have he := congrArg (atLine (K := K) none) hc
    have hm : aeval (4 * X : K[X]) (c 4) * X ^ 2 = 0 := by
      simpa [map_sum, atDiagonal_parameter_smul, parameterGenerators, Fin.sum_univ_succ,
        atLine_x, atLine_q, frameLineVariable, h0, h1, h2, h3] using he
    have hz : aeval (4 * X : K[X]) (c 4) = 0 :=
      (mul_eq_zero.mp hm).resolve_right (pow_ne_zero 2 X_ne_zero)
    have hz' : (c 4).comp (C (4 : K) * X) = 0 := by
      rw [comp_eq_aeval, map_ofNat]
      exact hz
    exact (comp_C_mul_X_eq_zero_iff (by simp [mem_nonZeroDivisors_iff_ne_zero])).mp hz'
  fin_cases i <;> assumption

/-- A free basis of the homogeneous coordinate ring over its regular parameter.
Its degrees are `0,1,1,1,2`. -/
noncomputable def parameterBasis [CharZero K] : Basis (Fin 5) K[X] (FrameCoordinateRing K) :=
  Basis.mk parameterGenerators_independent (by
    change ⊤ ≤ parameterSpan
    rw [parameterSpan_eq_top])

lemma parameterBasis_apply [CharZero K] (i : Fin 5) :
    parameterBasis (K := K) i = parameterGenerators i := Basis.mk_apply _ _ _

instance parameterModuleFree [CharZero K] : Module.Free K[X] (FrameCoordinateRing K) :=
  Module.Free.of_basis parameterBasis

instance parameterModuleFinite [CharZero K] : Module.Finite K[X] (FrameCoordinateRing K) :=
  Module.Finite.of_basis parameterBasis

end
end PfaffianDescent.FrameCoordinateRing
