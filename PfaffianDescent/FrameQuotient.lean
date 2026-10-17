import PfaffianDescent.FrameArtinSocle
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination

namespace PfaffianDescent
open scoped BigOperators

section
variable {K : Type*} [Field K]

/-- The five mixed-product relations and the linear form used in the appendix. -/
noncomputable def frameArtinRelations : Fin 6 → MvPolynomial (Fin 4) K :=
  let x : Fin 4 → MvPolynomial (Fin 4) K := MvPolynomial.X
  ![x 0 * x 2 - x 0 * x 1, x 0 * x 3 - x 0 * x 1,
    x 1 * x 2 - x 0 * x 1, x 1 * x 3 - x 0 * x 1,
    x 2 * x 3 - x 0 * x 1, x 0 + x 1 + x 2 + x 3]

noncomputable def frameArtinIdeal : Ideal (MvPolynomial (Fin 4) K) :=
  Ideal.span (Set.range (frameArtinRelations (K := K)))

abbrev FrameQuotient (K : Type*) [Field K] := MvPolynomial (Fin 4) K ⧸ frameArtinIdeal

namespace FrameQuotient

noncomputable def x (i : Fin 4) : FrameQuotient K :=
  Ideal.Quotient.mkₐ K (frameArtinIdeal (K := K)) (MvPolynomial.X i)

noncomputable def q : FrameQuotient K := x 0 * x 1

private theorem relation_zero (i : Fin 6) :
    Ideal.Quotient.mkₐ K (frameArtinIdeal (K := K)) (frameArtinRelations i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))

private theorem mixed02 : x (K := K) 0 * x 2 = q := by
  have h := relation_zero (K := K) 0
  change Ideal.Quotient.mkₐ K (frameArtinIdeal (K := K))
    (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0 at h
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  exact h

private theorem mixed03 : x (K := K) 0 * x 3 = q := by
  have h := relation_zero (K := K) 1
  change Ideal.Quotient.mkₐ K (frameArtinIdeal (K := K))
    (MvPolynomial.X 0 * MvPolynomial.X 3 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0 at h
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  exact h

private theorem mixed12 : x (K := K) 1 * x 2 = q := by
  have h := relation_zero (K := K) 2
  change Ideal.Quotient.mkₐ K (frameArtinIdeal (K := K))
    (MvPolynomial.X 1 * MvPolynomial.X 2 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0 at h
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  exact h

private theorem mixed13 : x (K := K) 1 * x 3 = q := by
  have h := relation_zero (K := K) 3
  change Ideal.Quotient.mkₐ K (frameArtinIdeal (K := K))
    (MvPolynomial.X 1 * MvPolynomial.X 3 - MvPolynomial.X 0 * MvPolynomial.X 1) = 0 at h
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at h
  exact h

private theorem mixed23 : x (K := K) 2 * x 3 = q := by
  have h := relation_zero (K := K) 4
  change Ideal.Quotient.mkₐ K (frameArtinIdeal (K := K))
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

theorem sum_variables : x (K := K) 0 + x 1 + x 2 + x 3 = 0 := by
  have h := relation_zero (K := K) 5
  change Ideal.Quotient.mkₐ K (frameArtinIdeal (K := K))
    (MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2 + MvPolynomial.X 3) = 0 at h
  simpa only [map_add, x] using h

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

theorem last_variable : x (K := K) 3 = -(x 0 + x 1 + x 2) := by
  linear_combination sum_variables (K := K)

/-- The squares in the Artinian reduction are all `-3q`. -/
theorem square (i : Fin 4) : x (K := K) i ^ 2 = -3 * q := by
  have h := congrArg (fun z : FrameQuotient K => x i * z) (sum_variables (K := K))
  rw [mul_zero] at h
  simp only [mul_add] at h
  have hm : ∀ j, i ≠ j → x (K := K) i * x j = q := mixed i
  fin_cases i
  · rw [hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)] at h
    change x (K := K) 0 * x 0 + q + q + q = 0 at h
    change x (K := K) 0 ^ 2 = -3 * q
    linear_combination h
  · rw [hm 0 (by decide), hm 2 (by decide), hm 3 (by decide)] at h
    change q + x (K := K) 1 * x 1 + q + q = 0 at h
    change x (K := K) 1 ^ 2 = -3 * q
    linear_combination h
  · rw [hm 0 (by decide), hm 1 (by decide), hm 3 (by decide)] at h
    change q + q + x (K := K) 2 * x 2 + q = 0 at h
    change x (K := K) 2 ^ 2 = -3 * q
    linear_combination h
  · rw [hm 0 (by decide), hm 1 (by decide), hm 2 (by decide)] at h
    change q + q + q + x (K := K) 3 * x 3 = 0 at h
    change x (K := K) 3 ^ 2 = -3 * q
    linear_combination h

end FrameQuotient
end

section
variable {K : Type*} [Field K] [CharZero K]
namespace FrameQuotient

/-- Every product of a variable with the degree-two class vanishes. -/
theorem variable_mul_q (i : Fin 4) : x (K := K) i * q = 0 := by
  have h := congrArg (fun z : FrameQuotient K => z * q) (sum_variables (K := K))
  simp only [add_mul, zero_mul] at h
  rw [variable_mul_q_eq 1 0, variable_mul_q_eq 2 0, variable_mul_q_eq 3 0] at h
  have hfour : (4 : K) • (x (K := K) 0 * q) = 0 := by
    rw [ofNat_smul_eq_nsmul, nsmul_eq_mul]
    linear_combination h
  have hzero : x (K := K) 0 * q = 0 :=
    (smul_eq_zero.mp hfour).resolve_left (by norm_num)
  rw [variable_mul_q_eq i 0, hzero]

end FrameQuotient
end
end PfaffianDescent
