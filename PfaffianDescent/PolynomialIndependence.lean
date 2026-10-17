import PfaffianDescent.PolynomialNormalization
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.LinearAlgebra.LinearIndependent.Defs

namespace PfaffianDescent
open Polynomial
open scoped BigOperators
attribute [local instance] Polynomial.algebra

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- Linear independence at a parameter implies linear independence of the
polynomial vectors over the ground polynomial ring. -/
theorem polynomial_independent_of_specialization (P : Fin n → L[X]) (t : K)
    (hP : LinearIndependent K (fun i => (P i).eval (algebraMap K L t))) :
    LinearIndependent K[X] P := by
  classical
  let f := algebraMap K L
  let Rel : (Fin n → K[X]) → Prop := fun q => ∑ i, (q i).map f * P i = 0
  have hstep : ∀ q, Rel ((X - C t) • q) → Rel q := by
    intro q h
    change (∑ i, (((X - C t) • q) i).map f * P i) = 0 at h
    simp only [Pi.smul_apply, smul_eq_mul, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C, mul_assoc, ← Finset.mul_sum] at h
    exact (mul_eq_zero.mp h).resolve_left (X_sub_C_ne_zero (f t))
  apply Fintype.linearIndependent_iff.mpr
  intro q hq
  have hrel : Rel q := by
    simpa only [Rel, f, Algebra.smul_def, Polynomial.algebraMap_def, Polynomial.coe_mapRingHom] using hq
  have hz : q = 0 := by
    by_contra hn
    obtain ⟨r, hr, j, hj⟩ := normalize_polynomial_relation t Rel hstep q hn hrel
    have hh := congrArg (evalRingHom (f t)) hr
    have he : ∑ i, (r i).eval t • (P i).eval (f t) = 0 := by
      simpa only [Rel, map_sum, map_mul, coe_evalRingHom, eval_map_apply, map_zero,
        Algebra.smul_def] using hh
    exact hj (Fintype.linearIndependent_iff.mp hP (fun i => (r i).eval t) he j)
  intro i
  exact congrFun hz i

end
end PfaffianDescent
