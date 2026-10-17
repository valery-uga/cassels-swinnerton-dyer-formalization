import PfaffianDescent.FrameParameterRelations

namespace PfaffianDescent.FrameCoordinateRing
open Polynomial Module
open scoped BigOperators
section
variable {K : Type*} [Field K]

/-- The polynomial parameter acts through the regular linear form. -/
noncomputable instance parameterAlgebra : Algebra K[X] (FrameCoordinateRing K) :=
  (aeval (ell (K := K))).toRingHom.toAlgebra

instance parameterScalarTower : IsScalarTower K K[X] (FrameCoordinateRing K) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  change algebraMap K (FrameCoordinateRing K) c = aeval ell (C c)
  exact (aeval_C ell c).symm

lemma parameter_smul (p : K[X]) (a : FrameCoordinateRing K) : p • a = aeval ell p * a := rfl

lemma parameter_X_smul (a : FrameCoordinateRing K) : (X : K[X]) • a = ell * a := by
  rw [parameter_smul, aeval_X]

lemma parameter_nat_smul (n : ℕ) (a : FrameCoordinateRing K) : (n : K[X]) • a = n * a := by
  rw [parameter_smul, map_natCast]

noncomputable def parameterGenerators : Fin 5 → FrameCoordinateRing K := ![1, x 0, x 1, x 2, q]

noncomputable def parameterSpan : Submodule K[X] (FrameCoordinateRing K) :=
  Submodule.span K[X] (Set.range parameterGenerators)

lemma parameterGenerators_mem (i : Fin 5) : parameterGenerators (K := K) i ∈ parameterSpan :=
  Submodule.subset_span (Set.mem_range_self i)

lemma parameterSpan_one : (1 : FrameCoordinateRing K) ∈ parameterSpan := parameterGenerators_mem 0

lemma parameterSpan_q : q (K := K) ∈ parameterSpan := parameterGenerators_mem 4

lemma parameterSpan_ell : ell (K := K) ∈ parameterSpan := by
  have h := (parameterSpan (K := K)).smul_mem (X : K[X]) parameterSpan_one
  simpa only [parameter_X_smul, mul_one] using h

lemma parameterSpan_x (i : Fin 4) : x (K := K) i ∈ parameterSpan := by
  fin_cases i
  · exact parameterGenerators_mem 1
  · exact parameterGenerators_mem 2
  · exact parameterGenerators_mem 3
  · change x (K := K) 3 ∈ parameterSpan
    rw [x_three_parameter]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.sub_mem _ parameterSpan_ell
      (parameterGenerators_mem 1)) (parameterGenerators_mem 2)) (parameterGenerators_mem 3)

lemma parameterSpan_x_mul_x (i j : Fin 4) : x (K := K) i * x j ∈ parameterSpan := by
  by_cases h : i = j
  · subst j
    rw [← pow_two, x_sq_parameter]
    have he := (parameterSpan (K := K)).sub_mem
      ((parameterSpan (K := K)).smul_mem (X : K[X]) (parameterSpan_x i))
      ((parameterSpan (K := K)).smul_mem (3 : K[X]) parameterSpan_q)
    have hthree : (3 : K[X]) • q (K := K) = 3 * q := parameter_nat_smul 3 q
    rw [parameter_X_smul, hthree] at he
    exact he
  · rw [mixed i j h]
    exact parameterSpan_q

lemma parameterSpan_x_mul_q [CharZero K] (i : Fin 4) : x (K := K) i * q ∈ parameterSpan := by
  rw [x_mul_q_parameter]
  apply (parameterSpan.restrictScalars K).smul_mem
  change ell * q ∈ parameterSpan
  have h := (parameterSpan (K := K)).smul_mem (X : K[X]) parameterSpan_q
  simpa only [parameter_X_smul] using h

lemma parameterSpan_mul_x [CharZero K] (a : FrameCoordinateRing K) (ha : a ∈ parameterSpan)
    (i : Fin 4) : a * x i ∈ parameterSpan := by
  apply Submodule.span_induction (p := fun a _ => a * x i ∈ parameterSpan) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨j, rfl⟩
    rw [mul_comm]
    fin_cases j
    · change x (K := K) i * 1 ∈ parameterSpan
      rw [mul_one]
      exact parameterSpan_x i
    · exact parameterSpan_x_mul_x i 0
    · exact parameterSpan_x_mul_x i 1
    · exact parameterSpan_x_mul_x i 2
    · exact parameterSpan_x_mul_q i
  · rw [zero_mul]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [add_mul]
    exact Submodule.add_mem _ ha hb
  · intro p a _ ha
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ p ha

/-- The homogeneous coordinate ring is generated over the regular polynomial
parameter by one constant, three linear classes, and one quadratic class. -/
theorem parameterSpan_eq_top [CharZero K] : parameterSpan (K := K) = ⊤ := by
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (frameIdeal (K := K)) a
  induction p using MvPolynomial.induction_on with
  | C c =>
      change (Ideal.Quotient.mkₐ K (frameIdeal (K := K)))
        (algebraMap K (MvPolynomial (Fin 4) K) c) ∈ parameterSpan
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      exact (parameterSpan.restrictScalars K).smul_mem c parameterSpan_one
  | add p q hp hq =>
      rw [map_add]
      exact Submodule.add_mem _ hp hq
  | mul_X p i hp =>
      rw [map_mul]
      exact parameterSpan_mul_x _ hp i

end
end PfaffianDescent.FrameCoordinateRing
