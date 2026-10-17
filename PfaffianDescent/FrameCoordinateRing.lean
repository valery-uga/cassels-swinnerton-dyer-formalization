import PfaffianDescent.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination

namespace PfaffianDescent
open scoped BigOperators

section
variable {K : Type*} [Field K]

/-- The five quadratic relations of the projective frame. -/
noncomputable def frameRelations : Fin 5 → MvPolynomial (Fin 4) K :=
  let x : Fin 4 → MvPolynomial (Fin 4) K := MvPolynomial.X
  ![x 0 * x 2 - x 0 * x 1, x 0 * x 3 - x 0 * x 1,
    x 1 * x 2 - x 0 * x 1, x 1 * x 3 - x 0 * x 1,
    x 2 * x 3 - x 0 * x 1]

noncomputable def frameIdeal : Ideal (MvPolynomial (Fin 4) K) :=
  Ideal.span (Set.range (frameRelations (K := K)))

abbrev FrameCoordinateRing (K : Type*) [Field K] := MvPolynomial (Fin 4) K ⧸ frameIdeal

namespace FrameCoordinateRing

noncomputable def x (i : Fin 4) : FrameCoordinateRing K :=
  Ideal.Quotient.mkₐ K (frameIdeal (K := K)) (MvPolynomial.X i)

noncomputable def q : FrameCoordinateRing K := x 0 * x 1

private theorem relation_zero (i : Fin 5) :
    Ideal.Quotient.mkₐ K (frameIdeal (K := K)) (frameRelations i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))

private theorem mixed02 : x (K := K) 0 * x 2 = q := by
  have h := relation_zero (K := K) 0
  change Ideal.Quotient.mkₐ K (frameIdeal (K := K))
    (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0 at h
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  exact h

private theorem mixed03 : x (K := K) 0 * x 3 = q := by
  have h := relation_zero (K := K) 1
  change Ideal.Quotient.mkₐ K (frameIdeal (K := K))
    (MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0 at h
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  exact h

private theorem mixed12 : x (K := K) 1 * x 2 = q := by
  have h := relation_zero (K := K) 2
  change Ideal.Quotient.mkₐ K (frameIdeal (K := K))
    (MvPolynomial.X 1 * MvPolynomial.X 2 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0 at h
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  exact h

private theorem mixed13 : x (K := K) 1 * x 3 = q := by
  have h := relation_zero (K := K) 3
  change Ideal.Quotient.mkₐ K (frameIdeal (K := K))
    (MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0 at h
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  exact h

private theorem mixed23 : x (K := K) 2 * x 3 = q := by
  have h := relation_zero (K := K) 4
  change Ideal.Quotient.mkₐ K (frameIdeal (K := K))
    (MvPolynomial.X 2 * MvPolynomial.X 3 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0 at h
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  exact h

/-- All six mixed products agree in the quotient. -/
theorem mixed (i j : Fin 4) (hij : i ≠ j) : x (K := K) i * x j = q := by
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · change x (K := K) 0 * x 1 = q
    rfl
  · change x (K := K) 0 * x 2 = q
    exact mixed02
  · change x (K := K) 0 * x 3 = q
    exact mixed03
  · change x (K := K) 1 * x 0 = q
    exact mul_comm _ _
  · exact False.elim (hij rfl)
  · change x (K := K) 1 * x 2 = q
    exact mixed12
  · change x (K := K) 1 * x 3 = q
    exact mixed13
  · change x (K := K) 2 * x 0 = q
    exact (mul_comm _ _).trans mixed02
  · change x (K := K) 2 * x 1 = q
    exact (mul_comm _ _).trans mixed12
  · exact False.elim (hij rfl)
  · change x (K := K) 2 * x 3 = q
    exact mixed23
  · change x (K := K) 3 * x 0 = q
    exact (mul_comm _ _).trans mixed03
  · change x (K := K) 3 * x 1 = q
    exact (mul_comm _ _).trans mixed13
  · change x (K := K) 3 * x 2 = q
    exact (mul_comm _ _).trans mixed23
  · exact False.elim (hij rfl)

/-- Multiplying the common mixed product by any variable gives the same cubic class. -/
theorem variable_mul_q_eq (i j : Fin 4) : x (K := K) i * q = x j * q := by
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨k, hik, hjk⟩ : ∃ k : Fin 4, i ≠ k ∧ j ≠ k := by
    fin_cases i <;> fin_cases j
    all_goals first | exact ⟨0, by decide, by decide⟩ | exact ⟨1, by decide, by decide⟩ | exact ⟨2, by decide, by decide⟩
  calc
    x i * q = x i * (x j * x k) := by rw [mixed j k hjk]
    _ = x j * (x i * x k) := by ring
    _ = x j * q := by rw [mixed i k hik]

theorem q_mul_power_eq (i j : Fin 4) (n : ℕ) :
    q * x (K := K) i ^ n = q * x j ^ n := by
  induction n with
  | zero => simp only [pow_zero, mul_one]
  | succ n ih =>
      calc
        q * x i ^ (n+1) = (q * x i ^ n) * x i := by rw [pow_succ, mul_assoc]
        _ = (q * x j ^ n) * x i := by rw [ih]
        _ = (x i * q) * x j ^ n := by ring
        _ = (x j * q) * x j ^ n := by rw [variable_mul_q_eq i j]
        _ = q * x j ^ (n+1) := by ring

theorem pure_mul_variable (i j : Fin 4) (n : ℕ) (hij : i ≠ j) :
    x (K := K) i ^ (n+1) * x j = q * x 0 ^ n := by
  calc
    x i ^ (n+1) * x j = (x i * x j) * x i ^ n := by ring
    _ = q * x i ^ n := by rw [mixed i j hij]
    _ = q * x 0 ^ n := q_mul_power_eq i 0 n

/-- Constant, positive pure powers, and one mixed monomial in each degree. -/
noncomputable def normalMonomial : Unit ⊕ ((Fin 4 × ℕ) ⊕ ℕ) → FrameCoordinateRing K
  | .inl _ => 1
  | .inr (.inl (i,n)) => x i ^ (n+1)
  | .inr (.inr n) => q * x 0 ^ n

noncomputable def normalSpan : Submodule K (FrameCoordinateRing K) :=
  Submodule.span K (Set.range normalMonomial)

theorem normalMonomial_mem (i) : normalMonomial (K := K) i ∈ normalSpan :=
  Submodule.subset_span (Set.mem_range_self i)

theorem normalMonomial_mul_variable_mem (j) (i : Fin 4) :
    normalMonomial (K := K) j * x i ∈ normalSpan := by
  rcases j with u | (⟨k,n⟩ | n)
  · simpa only [normalMonomial, one_mul, zero_add, pow_one]
      using normalMonomial_mem (K := K) (.inr (.inl (i,0)))
  · change x (K := K) k ^ (n+1) * x i ∈ normalSpan
    by_cases hki : k = i
    · subst k
      rw [← pow_succ]
      exact normalMonomial_mem (.inr (.inl (i,n+1)))
    · rw [pure_mul_variable k i n hki]
      exact normalMonomial_mem (.inr (.inr n))
  · change (q * x (K := K) 0 ^ n) * x i ∈ normalSpan
    have h : (q * x (K := K) 0 ^ n) * x i = q * x 0 ^ (n+1) := by
      calc
        _ = (x i * q) * x 0 ^ n := by ring
        _ = (x 0 * q) * x 0 ^ n := by rw [variable_mul_q_eq i 0]
        _ = _ := by ring
    rw [h]
    exact normalMonomial_mem (.inr (.inr (n+1)))

theorem mul_variable_mem (a : FrameCoordinateRing K) (ha : a ∈ normalSpan) (i : Fin 4) :
    a * x i ∈ normalSpan := by
  apply Submodule.span_induction (p := fun z _ => z * x i ∈ normalSpan) ?_ ?_ ?_ ?_ ha
  · rintro z ⟨j, rfl⟩
    exact normalMonomial_mul_variable_mem j i
  · rw [zero_mul]
    exact Submodule.zero_mem _
  · intro u v _ _ hu hv
    rw [add_mul]
    exact Submodule.add_mem _ hu hv
  · intro r u _ hu
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r hu

/-- The quadratic relations reduce every polynomial to the displayed normal monomials. -/
theorem normalSpan_eq_top : normalSpan (K := K) = ⊤ := by
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (frameIdeal (K := K)) a
  induction p using MvPolynomial.induction_on with
  | C c =>
      change (Ideal.Quotient.mkₐ K (frameIdeal (K := K)))
        (algebraMap K (MvPolynomial (Fin 4) K) c) ∈ normalSpan
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ c (normalMonomial_mem (.inl ()))
  | add p q hp hq =>
      rw [map_add]
      exact Submodule.add_mem _ hp hq
  | mul_X p i hp =>
      rw [map_mul]
      exact mul_variable_mem _ hp i

end FrameCoordinateRing
end
end PfaffianDescent
