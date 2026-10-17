import AllCharacteristics.ProjectiveClassifyingMap

/-!
# Scalar invariance of projective equation parameters

Multiplying a field equation by a nonzero scalar leaves its normalized chart
map, and hence its coefficient-independent projective classifying morphism,
unchanged.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable {R k : Type u} [CommRing R] [Field k] {σ : Type} {d : ℕ}
variable (b : R →+* k) (p : MvPolynomial σ k) (a : k) (ha : a ≠ 0)
variable (j : Monomials σ d) (hj : p.coeff j.1 ≠ 0)
attribute [local instance] MvPolynomial.gradedAlgebra
include ha

/-- Scaling an equation leaves its normalized coefficient-chart map unchanged. -/
theorem projectiveEquationChartMap_C_mul
    (haj : (C a * p).coeff j.1 ≠ 0) :
    projectiveEquationChartMap b (C a * p) j haj = projectiveEquationChartMap b p j hj := by
  apply projectiveChartMap_ext j
  · apply RingHom.ext
    intro r
    exact (projectiveEquationChartMap_baseMap b (C a * p) j haj r).trans
      (projectiveEquationChartMap_baseMap b p j hj r).symm
  · intro m
    rw [projectiveEquationChartMap_coordinate, projectiveEquationChartMap_coordinate,
      coeff_C_mul, coeff_C_mul, mul_inv_rev, mul_assoc, ← mul_assoc a⁻¹,
      inv_mul_cancel₀ ha, one_mul]

/-- The projective parameter computed in a chosen chart is invariant under nonzero scaling. -/
theorem projectiveEquationParameter_C_mul (haj : (C a * p).coeff j.1 ≠ 0) :
    projectiveEquationParameter b (C a * p) j haj = projectiveEquationParameter b p j hj := by
  unfold projectiveEquationParameter
  rw [projectiveEquationChartMap_C_mul b p a ha j hj haj]

/-- The coefficient-independent classifying morphism depends only on the
projective class of the nonzero homogeneous equation. -/
theorem projectiveClassifyingMap_C_mul (hp : p.IsHomogeneous d) (hne : p ≠ 0)
    (hane : C a * p ≠ 0) :
    projectiveClassifyingMap (C a * p) (hp.C_mul a) hane b =
      projectiveClassifyingMap p hp hne b := by
  let i := chosenEquationCoefficient p hp hne
  have hi : p.coeff i.1 ≠ 0 := chosenEquationCoefficient_ne_zero p hp hne
  have hai : (C a * p).coeff i.1 ≠ 0 := by
    rw [coeff_C_mul]
    exact mul_ne_zero ha hi
  rw [projectiveClassifyingMap_eq_chart (C a * p) (hp.C_mul a) hane b i hai,
    projectiveClassifyingMap_eq_chart p hp hne b i hi]
  exact projectiveEquationParameter_C_mul b p a ha i hi hai

end UniversalHomogeneous
end AllCharacteristics
