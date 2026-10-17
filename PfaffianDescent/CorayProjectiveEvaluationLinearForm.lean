import PfaffianDescent.CorayExplicitProjectiveEvaluationPoint
import Mathlib.Algebra.BigOperators.Field

/-! Source-only / unverified. The actual projective chart evaluates an
original-coefficient linear form to its exact normalized coordinate sum.
A nonzero chart entry removes the denominator. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {K F : Type u} [CommRing K] [Field F] {σ : Type} [Fintype σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The chart expression of an original-K projective linear equation. -/
def projectiveChartLinearForm (a : σ) (c : σ → K) :
    ChartRing (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a :=
  ∑ i, chartBaseMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a
    (c i) * chartCoordinate (⊥ : HomogeneousIdeal
      (MvPolynomial.homogeneousSubmodule σ K)) a i

/-- Exact evaluation of the linear equation by the actual chart map. -/
theorem projectiveEvaluationChartMap_linearForm (φ : K →+* F) (x : σ → F)
    (a : σ) (ha : x a ≠ 0) (c : σ → K) :
    projectiveEvaluationChartMap φ x a ha (projectiveChartLinearForm a c) =
      ∑ i, φ (c i) * (x i / x a) := by
  simp only [projectiveChartLinearForm, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hc : projectiveEvaluationChartMap φ x a ha
      (chartBaseMap (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) a
        (c i)) = φ (c i) := by
    simpa only [RingHom.comp_apply] using
      RingHom.congr_fun (projectiveEvaluationChartMap_base φ x a ha) (c i)
  rw [hc, projectiveEvaluationChartMap_coordinate]

/-- The nonzero coordinate denominator cannot create or remove a
linear equation at this actual projective point. -/
theorem projectiveEvaluationChartMap_linearForm_zero_iff (φ : K →+* F)
    (x : σ → F) (a : σ) (ha : x a ≠ 0) (c : σ → K) :
    projectiveEvaluationChartMap φ x a ha (projectiveChartLinearForm a c) = 0 ↔
      ∑ i, φ (c i) * x i = 0 := by
  rw [projectiveEvaluationChartMap_linearForm]
  have hsum : (∑ i, φ (c i) * (x i / x a)) =
      (∑ i, φ (c i) * x i) / x a := by
    simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]
  rw [hsum, div_eq_zero_iff]
  simp only [ha, or_false]

end PfaffianDescent.Coray
end
