import PfaffianDescent.FrameCoordinateRingExact
import Mathlib.RingTheory.MvPolynomial.Homogeneous

namespace PfaffianDescent.FrameCoordinateRing
open Module
open scoped BigOperators Pointwise

section
variable {K : Type*} [Field K]

/-- The actual degree-`d` part of the quotient of the polynomial ring. -/
noncomputable def component (d : ℕ) : Submodule K (FrameCoordinateRing K) :=
  (MvPolynomial.homogeneousSubmodule (Fin 4) K d).map
    (Ideal.Quotient.mkₐ K (frameIdeal (K := K))).toLinearMap

noncomputable def highGenerator (n : ℕ) : Option (Fin 4) → FrameCoordinateRing K
  | none => q * x 0 ^ n
  | some i => x i ^ (n+2)

noncomputable def highSpan (n : ℕ) : Submodule K (FrameCoordinateRing K) :=
  Submodule.span K (Set.range (highGenerator n))

theorem highGenerator_mem (n : ℕ) (i) : highGenerator (K := K) n i ∈ highSpan n :=
  Submodule.subset_span (Set.mem_range_self i)

theorem component_one : component (K := K) 1 = Submodule.span K (Set.range x) := by
  rw [component, MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span]
  rw [← Set.range_comp]
  rfl

theorem component_pow (d : ℕ) : component (K := K) d = component 1 ^ d := by
  rw [component, ← MvPolynomial.homogeneousSubmodule_one_pow,
    Submodule.map_pow]
  rfl

theorem component_succ (d : ℕ) : component (K := K) (d+1) = component d * component 1 := by
  rw [component_pow (d+1), Submodule.pow_succ, ← component_pow]

theorem highGenerator_mem_component (n : ℕ) (i) :
    highGenerator (K := K) n i ∈ component (n+2) := by
  cases i with
  | some j =>
      refine ⟨MvPolynomial.X j ^ (n+2), MvPolynomial.isHomogeneous_X_pow j (n+2), ?_⟩
      exact map_pow (Ideal.Quotient.mkₐ K (frameIdeal (K := K))) _ _
  | none =>
      refine ⟨MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 0 ^ n, ?_, ?_⟩
      · change MvPolynomial.IsHomogeneous _ (n+2)
        have h := ((MvPolynomial.isHomogeneous_X K (0 : Fin 4)).mul
          (MvPolynomial.isHomogeneous_X K (1 : Fin 4))).mul
            (MvPolynomial.isHomogeneous_X_pow (R := K) (0 : Fin 4) n)
        simpa only [Nat.add_comm] using h
      · change (Ideal.Quotient.mkₐ K (frameIdeal (K := K)))
          (MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 0 ^ n) = q * x 0 ^ n
        simp only [map_mul, map_pow]
        rfl

theorem highSpan_le_component (n : ℕ) : highSpan (K := K) n ≤ component (n+2) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact highGenerator_mem_component n i

theorem highGenerator_mul_variable_mem (n : ℕ) (p : Option (Fin 4)) (i : Fin 4) :
    highGenerator (K := K) n p * x i ∈ highSpan (n+1) := by
  cases p with
  | none =>
      change (q * x (K := K) 0 ^ n) * x i ∈ highSpan (n+1)
      have h : (q * x (K := K) 0 ^ n) * x i = q * x 0 ^ (n+1) := by
        calc
          _ = (x i * q) * x 0 ^ n := by ring
          _ = (x 0 * q) * x 0 ^ n := by rw [variable_mul_q_eq i 0]
          _ = _ := by ring
      rw [h]
      exact highGenerator_mem (n+1) none
  | some j =>
      change x (K := K) j ^ (n+2) * x i ∈ highSpan (n+1)
      by_cases hji : j = i
      · subst j
        rw [← pow_succ]
        exact highGenerator_mem (n+1) (some i)
      · rw [pure_mul_variable j i (n+1) hji]
        exact highGenerator_mem (n+1) none

theorem highSpan_mul_component_one_le (n : ℕ) :
    highSpan (K := K) n * component 1 ≤ highSpan (n+1) := by
  rw [component_one, highSpan, Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ⟨p, rfl⟩, b, ⟨i, rfl⟩, rfl⟩
  exact highGenerator_mul_variable_mem n p i

theorem component_two_le : component (K := K) 2 ≤ highSpan 0 := by
  rw [component_succ 1, component_one, Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
  change x (K := K) i * x j ∈ highSpan 0
  by_cases hij : i = j
  · subst i
    rw [← pow_two]
    exact highGenerator_mem 0 (some j)
  · rw [mixed i j hij]
    simpa only [highGenerator, pow_zero, mul_one] using highGenerator_mem (K := K) 0 none

/-- In every degree at least two the four pure powers and one mixed monomial span. -/
theorem component_high (n : ℕ) : component (K := K) (n+2) = highSpan n := by
  apply le_antisymm ?_ (highSpan_le_component n)
  induction n with
  | zero => exact component_two_le
  | succ n ih =>
      rw [show n+1+2 = (n+2)+1 by omega, component_succ]
      exact (Submodule.smul_mono_left ih).trans (highSpan_mul_component_one_le n)

end
end PfaffianDescent.FrameCoordinateRing
