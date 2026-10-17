import PfaffianDescent.QuarticFiniteNet
import PfaffianDescent.QuarticTwistedCubicIdeal
import PfaffianDescent.PolynomialLinearChange

/-!
# Polynomial parametrization in the exceptional base-locus branch

These small identities avoid expanding the coordinate change all at once.
They prove directly that the three cleared-denominator quadrics vanish on the
binary-cubic parametrization when `Δ = 0`.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial

variable {K : Type*} [Field K]

noncomputable def exceptionalTwistedCubicParam (a b c d e : K) :
    MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 2) K :=
  MvPolynomial.aeval
    ![C a * X 0 * (C d * X 0 - C b * X 1) * (C e * X 0 - C c * X 1),
      C a * X 1 * (C d * X 0 - C b * X 1) * (C e * X 0 - C c * X 1),
      C b * C d * X 0 * X 1 * (C e * X 0 - C c * X 1),
      C c * C e * X 0 * X 1 * (C d * X 0 - C b * X 1)]

theorem exceptionalTwistedCubicParam_eq_coordinate_change (a b c d e : K) :
    exceptionalTwistedCubicParam a b c d e =
      (standardTwistedCubicParam K).comp
        (linearSubstitution (baseLocusCubicCoefficientMatrix a b c d e)) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, linearSubstitution_X]
  change exceptionalTwistedCubicParam a b c d e (X i) =
    standardTwistedCubicParam K
      (∑ j, C (baseLocusCubicCoefficientMatrix a b c d e i j) * X j)
  rw [map_sum]
  fin_cases i <;>
    simp [exceptionalTwistedCubicParam, standardTwistedCubicParam,
      baseLocusCubicCoefficientMatrix, Fin.sum_univ_four] <;> ring

theorem exceptionalTwistedCubicParam_scaled_quadric_zero_0
    (a b c d e f : K) :
    exceptionalTwistedCubicParam a b c d e
      (scaledBaseLocusQuadricPolynomials a b c d e f 0) = 0 := by
  simp [exceptionalTwistedCubicParam, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric]
  ring

theorem exceptionalTwistedCubicParam_scaled_quadric_zero_1
    (a b c d e f : K) :
    exceptionalTwistedCubicParam a b c d e
      (scaledBaseLocusQuadricPolynomials a b c d e f 1) = 0 := by
  simp [exceptionalTwistedCubicParam, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric]
  ring

theorem exceptionalTwistedCubicParam_scaled_quadric_2_formula
    (a b c d e f : K) :
    exceptionalTwistedCubicParam a b c d e
      (scaledBaseLocusQuadricPolynomials a b c d e f 2) =
      C b * C c * X 0 ^ 2 * X 1 ^ 2 * (C d * X 0 - C b * X 1) *
        (C e * X 0 - C c * X 1) * C (baseLocusDelta a b c d e f) := by
  simp [exceptionalTwistedCubicParam, scaledBaseLocusQuadricPolynomials,
    scaledBaseLocusQuadrics, offDiagonalQuadric, baseLocusDelta]
  ring

theorem exceptionalTwistedCubicParam_scaled_quadric_zero_2
    (a b c d e f : K) (hdelta : baseLocusDelta a b c d e f = 0) :
    exceptionalTwistedCubicParam a b c d e
      (scaledBaseLocusQuadricPolynomials a b c d e f 2) = 0 := by
  rw [exceptionalTwistedCubicParam_scaled_quadric_2_formula, hdelta]
  simp

theorem exceptionalTwistedCubicParam_scaled_quadric_zero
    (a b c d e f : K) (hdelta : baseLocusDelta a b c d e f = 0) (i : Fin 3) :
    exceptionalTwistedCubicParam a b c d e
      (scaledBaseLocusQuadricPolynomials a b c d e f i) = 0 := by
  fin_cases i
  · exact exceptionalTwistedCubicParam_scaled_quadric_zero_0 a b c d e f
  · exact exceptionalTwistedCubicParam_scaled_quadric_zero_1 a b c d e f
  · exact exceptionalTwistedCubicParam_scaled_quadric_zero_2 a b c d e f hdelta

end QuarticNet
end PfaffianDescent
