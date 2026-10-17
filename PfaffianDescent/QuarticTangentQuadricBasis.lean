import PfaffianDescent.QuarticFiniteNet
import PfaffianDescent.QuarticGeneralTangentQuadrics

/-!
# The quadric basis of a full-support tangent net

For a skew tangent matrix with its first row nonzero, the three displayed
scaled quadrics span every homogeneous quadric through the four tangent
dual points.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial Module

variable {K : Type*} [Field K]

theorem tangent_quadric_kernel_span_scaled
    (a b c d e f : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (q : Fin 6 → K)
    (hq : q ∈ LinearMap.ker
      (tangentQuadricEvaluationLinearMap (skewTangentDirections a b c d e f))) :
    ∃ r : Fin 3 → K,
      q = ∑ i, r i • scaledBaseLocusQuadrics a b c d e f i := by
  let r : Fin 3 → K := ![q 3 / (a * b), q 4 / (a * c), q 5 / (b * c)]
  refine ⟨r, ?_⟩
  change tangentQuadricEvaluation (skewTangentDirections a b c d e f) q = 0 at hq
  have h0 : q 0 * a + q 1 * b + q 2 * c = 0 := by
    simpa [tangentQuadricEvaluation, skewTangentDirections] using congrFun hq 0
  have h1 : q 0 * (-a) + q 3 * d + q 4 * e = 0 := by
    simpa [tangentQuadricEvaluation, skewTangentDirections] using congrFun hq 1
  have h2 : q 1 * (-b) + q 3 * (-d) + q 5 * f = 0 := by
    simpa [tangentQuadricEvaluation, skewTangentDirections] using congrFun hq 2
  funext j
  fin_cases j
  · simp [r, scaledBaseLocusQuadrics, Fin.sum_univ_three]
    field_simp [ha, hb, hc]
    linear_combination -h1
  · simp [r, scaledBaseLocusQuadrics, Fin.sum_univ_three]
    field_simp [ha, hb, hc]
    linear_combination -h2
  · simp [r, scaledBaseLocusQuadrics, Fin.sum_univ_three]
    field_simp [ha, hb, hc]
    linear_combination h0 + h1 + h2
  · simp [r, scaledBaseLocusQuadrics, Fin.sum_univ_three]
    field_simp [ha, hb, hc]
  · simp [r, scaledBaseLocusQuadrics, Fin.sum_univ_three]
    field_simp [ha, hb, hc]
  · simp [r, scaledBaseLocusQuadrics, Fin.sum_univ_three]
    field_simp [ha, hb, hc]

theorem offDiagonalQuadrics_scaledBaseLocus
    (a b c d e f : K) (i : Fin 3) :
    offDiagonalQuadrics (scaledBaseLocusQuadrics a b c d e f i) =
      scaledBaseLocusQuadricPolynomials a b c d e f i := by
  fin_cases i <;>
    simp [offDiagonalQuadrics, offDiagonalCoefficientEmbedding, homogeneousAffineQuadrics,
      Fintype.linearCombination_apply, homogeneousAffineQuadricExponent,
      scaledBaseLocusQuadrics, scaledBaseLocusQuadricPolynomials,
      offDiagonalQuadric, Fin.sum_univ_succ, smul_monomial, X, C_mul',
      pow_two, monomial_mul, ← Finsupp.single_add] <;> ring

/-- Every homogeneous quadric through the four tangent dual points belongs to
the ideal of the three scaled base-locus quadrics. -/
theorem homogeneous_tangent_quadric_mem_scaledBaseLocus_ideal
    (a b c d e f : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 2)
    (hvan : ∀ i : Fin 4,
      aeval (tangentDualPoint (skewTangentDirections a b c d e f) i) F = 0) :
    F ∈ Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)) := by
  have hdiag : ∀ i : Fin 4, skewTangentDirections a b c d e f i i = 0 := by
    intro i
    fin_cases i <;> rfl
  obtain ⟨q, hq, hqF⟩ := homogeneous_quadric_is_offDiagonal
    (skewTangentDirections a b c d e f) hdiag F hF hvan
  obtain ⟨r, hr⟩ := tangent_quadric_kernel_span_scaled a b c d e f ha hb hc q hq
  rw [← hqF, hr, map_sum]
  apply Ideal.sum_mem
  intro i _
  rw [map_smul, offDiagonalQuadrics_scaledBaseLocus]
  rw [smul_eq_C_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i))

end QuarticNet
end PfaffianDescent
