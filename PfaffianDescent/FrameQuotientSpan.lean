import PfaffianDescent.FrameQuotient
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace PfaffianDescent.FrameQuotient
open Module
open scoped BigOperators

section
variable {K : Type*} [Field K] [CharZero K]

noncomputable def generators : Vec (FrameQuotient K) 5 := ![1, x 0, x 1, x 2, q]

noncomputable def normalSpan : Submodule K (FrameQuotient K) :=
  Submodule.span K (Set.range generators)

theorem generator_mem (j : Fin 5) : generators (K := K) j ∈ normalSpan :=
  Submodule.subset_span (Set.mem_range_self j)

theorem variable_mem (i : Fin 4) : x (K := K) i ∈ normalSpan := by
  fin_cases i
  · exact generator_mem 1
  · exact generator_mem 2
  · exact generator_mem 3
  · change x (K := K) 3 ∈ normalSpan
    rw [last_variable]
    exact Submodule.neg_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ (generator_mem 1) (generator_mem 2)) (generator_mem 3))

theorem variables_mul_mem (i j : Fin 4) : x (K := K) i * x j ∈ normalSpan := by
  by_cases hij : i = j
  · rw [hij, ← pow_two, square]
    have he : (-3 : FrameQuotient K) * q = -(q + q + q) := by ring
    rw [he]
    exact Submodule.neg_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ (generator_mem 4) (generator_mem 4)) (generator_mem 4))
  · rw [mixed i j hij]
    exact generator_mem 4

theorem generator_mul_variable_mem (j : Fin 5) (i : Fin 4) :
    generators (K := K) j * x i ∈ normalSpan := by
  fin_cases j
  · change 1 * x (K := K) i ∈ normalSpan
    rw [one_mul]
    exact variable_mem i
  · exact variables_mul_mem 0 i
  · exact variables_mul_mem 1 i
  · exact variables_mul_mem 2 i
  · change q * x (K := K) i ∈ normalSpan
    rw [mul_comm, variable_mul_q]
    exact Submodule.zero_mem _

theorem mul_variable_mem (a : FrameQuotient K) (ha : a ∈ normalSpan) (i : Fin 4) :
    a * x i ∈ normalSpan := by
  apply Submodule.span_induction (p := fun z _ => z * x i ∈ normalSpan) ?_ ?_ ?_ ?_ ha
  · rintro z ⟨j, rfl⟩
    exact generator_mul_variable_mem j i
  · rw [zero_mul]
    exact Submodule.zero_mem _
  · intro u v _ _ hu hv
    rw [add_mul]
    exact Submodule.add_mem _ hu hv
  · intro r u _ hu
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ r hu

/-- Every residue class is a linear combination of `1,x₀,x₁,x₂,q`. -/
theorem normalSpan_eq_top : normalSpan (K := K) = ⊤ := by
  apply top_unique
  intro a ha
  clear ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (frameArtinIdeal (K := K)) a
  induction p using MvPolynomial.induction_on with
  | C c =>
      change (Ideal.Quotient.mkₐ K (frameArtinIdeal (K := K)))
        (algebraMap K (MvPolynomial (Fin 4) K) c) ∈ normalSpan
      rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ c (generator_mem 0)
  | add p q hp hq =>
      rw [map_add]
      exact Submodule.add_mem _ hp hq
  | mul_X p i hp =>
      rw [map_mul]
      exact mul_variable_mem _ hp i

instance : FiniteDimensional K (FrameQuotient K) := by
  apply Module.Finite.of_surjective (Fintype.linearCombination K (generators (K := K)))
  rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
  exact normalSpan_eq_top

end
end PfaffianDescent.FrameQuotient
