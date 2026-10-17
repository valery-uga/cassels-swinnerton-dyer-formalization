import PfaffianDescent.QuarticFourCycleNet
import PfaffianDescent.QuarticGeneralTangentQuadrics

/-!
# The quadric basis of the four-cycle tangent net

The three scaled four-cycle quadrics span every homogeneous quadric through
the four corresponding tangent dual points.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module

variable {K : Type*} [Field K]

theorem four_cycle_tangent_quadric_kernel_span_scaled
    (b c d e : K) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (q : Fin 6 → K)
    (hq : q ∈ LinearMap.ker
      (tangentQuadricEvaluationLinearMap (skewTangentDirections 0 b c d e 0))) :
    ∃ r : Fin 3 → K,
      q = ∑ i, r i • fourCycleScaledQuadrics b c d e i := by
  let r : Fin 3 → K := ![q 0, q 5, q 1 / (c * d * e)]
  refine ⟨r, ?_⟩
  change tangentQuadricEvaluation (skewTangentDirections 0 b c d e 0) q = 0 at hq
  have h0 : q 1 * b + q 2 * c = 0 := by
    simpa [tangentQuadricEvaluation, skewTangentDirections] using congrFun hq 0
  have h1 : q 3 * d + q 4 * e = 0 := by
    simpa [tangentQuadricEvaluation, skewTangentDirections] using congrFun hq 1
  have h2 : q 1 * (-b) + q 3 * (-d) = 0 := by
    simpa [tangentQuadricEvaluation, skewTangentDirections] using congrFun hq 2
  funext j
  fin_cases j
  · simp [r, fourCycleScaledQuadrics, Fin.sum_univ_three]
  · simp [r, fourCycleScaledQuadrics, Fin.sum_univ_three]
    field_simp [hb, hc, hd, he]
  · simp [r, fourCycleScaledQuadrics, Fin.sum_univ_three]
    field_simp [hb, hc, hd, he]
    linear_combination h0
  · simp [r, fourCycleScaledQuadrics, Fin.sum_univ_three]
    field_simp [hb, hc, hd, he]
    linear_combination -h2
  · simp [r, fourCycleScaledQuadrics, Fin.sum_univ_three]
    field_simp [hb, hc, hd, he]
    linear_combination h1 + h2
  · simp [r, fourCycleScaledQuadrics, Fin.sum_univ_three]

theorem offDiagonalQuadrics_fourCycleScaled
    (b c d e : K) (i : Fin 3) :
    offDiagonalQuadrics (fourCycleScaledQuadrics b c d e i) =
      fourCycleScaledQuadricPolynomials b c d e i := by
  fin_cases i <;>
    simp [offDiagonalQuadrics, offDiagonalCoefficientEmbedding, homogeneousAffineQuadrics,
      Fintype.linearCombination_apply, homogeneousAffineQuadricExponent,
      fourCycleScaledQuadrics, fourCycleScaledQuadricPolynomials,
      offDiagonalQuadric, Fin.sum_univ_succ, smul_monomial, X, C_mul',
      monomial_mul] <;> ring

theorem homogeneous_tangent_quadric_mem_fourCycleScaled_ideal
    (b c d e : K) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 2)
    (hvan : ∀ i : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections 0 b c d e 0) i) F = 0) :
    F ∈ Ideal.span (Set.range (fourCycleScaledQuadricPolynomials b c d e)) := by
  have hdiag : ∀ i : Fin 4, skewTangentDirections 0 b c d e 0 i i = 0 := by
    intro i
    fin_cases i <;> rfl
  obtain ⟨q, hq, hqF⟩ := homogeneous_quadric_is_offDiagonal
    (skewTangentDirections 0 b c d e 0) hdiag F hF hvan
  obtain ⟨r, hr⟩ := four_cycle_tangent_quadric_kernel_span_scaled
    b c d e hb hc hd he q hq
  rw [← hqF, hr, map_sum]
  apply Ideal.sum_mem
  intro i _
  rw [map_smul, offDiagonalQuadrics_fourCycleScaled, smul_eq_C_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

end QuarticNet
end PfaffianDescent
