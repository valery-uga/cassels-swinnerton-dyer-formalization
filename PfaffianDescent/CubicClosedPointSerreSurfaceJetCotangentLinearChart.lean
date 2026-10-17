import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNormalization

/-! The actual common linear chart map of a normalized square-zero jet. -/
noncomputable section
open AlgebraicGeometry MvPolynomial TrivSqZeroExt HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The native normalized jet vanishes on the actual cubic equation ideal. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_ideal_zero
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (ell : MvPolynomial (Fin 4) K) (J : Fin 4 → CubicSurfaceFirstJet K)
    (hunit : IsUnit (aeval J ell)) (hzero : aeval J p = 0) :
    ∀ q ∈ (equationIdeal p hp).toIdeal,
      q.eval₂ (algebraMap K (CubicSurfaceFirstJet K))
        (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet ell J hunit) = 0 := by
  intro q hq
  change q ∈ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) at hq
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp hq
  rw [hr, eval₂_mul]
  have hpzero := cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_cubic
    ell J hunit p hp hzero
  change eval₂ (algebraMap K _) _ p = 0 at hpzero
  rw [hpzero, zero_mul]

/-- The actual square-zero map from the actual common linear affine chart. -/
def cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (J : Fin 4 → CubicSurfaceFirstJet K)
    (hunit : IsUnit (aeval J ell)) (hzero : aeval J p = 0) :
    Away (grading (equationIdeal p hp))
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell) →+* CubicSurfaceFirstJet K :=
  linearNormalizedPointChartMap (equationIdeal p hp)
    (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet ell J hunit) ell
    (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_ell ell J hell hunit)
    (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_ideal_zero
      p hp ell J hunit hzero)

/-- The actual affine chart polynomial germ evaluates to q/ell^d. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap_homogeneous
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (J : Fin 4 → CubicSurfaceFirstJet K)
    (hunit : IsUnit (aeval J ell)) (hzero : aeval J p = 0)
    (q : MvPolynomial (Fin 4) K) {d : ℕ} (hq : q.IsHomogeneous d) :
    cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap p hp ell hell J hunit hzero
      (q.eval₂ (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal p hp)))
        (linearChartCoordinate (equationIdeal p hp)
          (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)
          (polynomial_class_mem_grading (equationIdeal p hp) ell hell))) =
      (↑hunit.unit⁻¹ : CubicSurfaceFirstJet K) ^ d * aeval J q := by
  exact (linearNormalizedPointChartMap_eval (equationIdeal p hp)
    (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet ell J hunit) ell hell
    (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_ell ell J hell hunit)
    (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_ideal_zero p hp ell J hunit hzero)
    q).trans (cubicClosedPointSerreSurfaceJetCotangent_normalizedJet_homogeneous ell J hunit q hq)

/-- Full cubic jet interpolation makes the actual common-chart quotient
surjective after normalization by the actual unit ell(J). -/
theorem cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap_surjective
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (J : Fin 4 → CubicSurfaceFirstJet K)
    (hunit : IsUnit (aeval J ell)) (hzero : aeval J p = 0)
    (hjets : Function.Surjective
      (fun q : homogeneousSubmodule (Fin 4) K 3 => aeval J q.1)) :
    Function.Surjective
      (cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap p hp ell hell J hunit hzero) := by
  intro v
  obtain ⟨q, hq⟩ := hjets ((↑hunit.unit : CubicSurfaceFirstJet K) ^ 3 * v)
  refine ⟨q.1.eval₂ (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal p hp)))
    (linearChartCoordinate (equationIdeal p hp)
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)
      (polynomial_class_mem_grading (equationIdeal p hp) ell hell)), ?_⟩
  rw [cubicClosedPointSerreSurfaceJetCotangent_linearChartJetMap_homogeneous
    p hp ell hell J hunit hzero q.1 q.2]
  change aeval J q.1 = _ at hq
  rw [hq, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]

end PfaffianDescent
