import PfaffianDescent.VoisinExplicitSeparableFourLineExample
import AllCharacteristics.SmoothCubicReference

/-!
# Smoothness of the explicit separable four-line cubic

The same diagonal cubic that certifies nonzero four-line discriminants is
smooth in characteristic zero. The proof is by projective-chart Jacobian
certificates, with the diagonal coefficient at each chart inverted.
-/

namespace PfaffianDescent.VoisinExplicitSeparableFourLineExample

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem p₀_smooth
    {K : Type u} [Field K] [CharZero K] :
    Smooth (hypersurfaceToBase (p₀ (K := K)) p₀_homogeneous) := by
  have h3 : (3 : K) ≠ 0 := by norm_num
  have h2 : (2 : K) ≠ 0 := by norm_num
  have h6 : (6 : K) ≠ 0 := by norm_num
  have h9 : (9 : K) ≠ 0 := by norm_num
  have hnat3 : (C (3 : K) : MvPolynomial (Fin 4) K) = 3 :=
    map_natCast C 3
  have hC3 : (C ((3 : K)⁻¹) : MvPolynomial (Fin 4) K) * 3 = 1 := by
    rw [← hnat3, ← C_mul]
    simp [h3]
  have hC2 : (C ((2 : K)⁻¹) : MvPolynomial (Fin 4) K) * C 2 = 1 := by
    rw [← C_mul]
    simp [h2]
  have hC6 : (C ((6 : K)⁻¹) : MvPolynomial (Fin 4) K) * 3 = C ((2 : K)⁻¹) := by
    rw [← hnat3, ← C_mul]
    congr 1
    field_simp
    ring
  have hC9 : (C ((9 : K)⁻¹) : MvPolynomial (Fin 4) K) * 3 = C ((3 : K)⁻¹) := by
    rw [← hnat3, ← C_mul]
    congr 1
    field_simp
    ring
  apply smooth_hypersurface_of_chart_pderiv_span
  intro j
  fin_cases j
  · apply span_chartPDeriv_eq_top_of_three_certificate
      p₀ p₀_homogeneous 0 1 2 3
      (by decide) (by decide) (by decide)
      1 (-(X 0 ^ 2 + X 0 + 1))
      (-(C (3 : K)⁻¹ * X 1))
      (-(C (3 : K)⁻¹ * X 2))
      (-(C (3 : K)⁻¹ * X 3))
    simp [p₀]
    linear_combination
      -(X 1 ^ 3 + C (2 : K) * X 2 ^ 3 + C (3 : K) * X 3 ^ 3) * hC3
  · apply span_chartPDeriv_eq_top_of_three_certificate
      p₀ p₀_homogeneous 1 0 2 3
      (by decide) (by decide) (by decide)
      1 (-(X 1 ^ 2 + X 1 + 1))
      (-(C (3 : K)⁻¹ * X 0))
      (-(C (3 : K)⁻¹ * X 2))
      (-(C (3 : K)⁻¹ * X 3))
    simp [p₀]
    linear_combination
      -(X 0 ^ 3 + C (2 : K) * X 2 ^ 3 + C (3 : K) * X 3 ^ 3) * hC3
  · apply span_chartPDeriv_eq_top_of_three_certificate
      p₀ p₀_homogeneous 2 0 1 3
      (by decide) (by decide) (by decide)
      (C (2 : K)⁻¹) (-(X 2 ^ 2 + X 2 + 1))
      (-(C (6 : K)⁻¹ * X 0))
      (-(C (6 : K)⁻¹ * X 1))
      (-(C (6 : K)⁻¹ * X 3))
    simp [p₀]
    linear_combination
      -(X 0 ^ 3 + X 1 ^ 3 + C (3 : K) * X 3 ^ 3) * hC6 +
      X 2 ^ 3 * hC2
  · apply span_chartPDeriv_eq_top_of_three_certificate
      p₀ p₀_homogeneous 3 0 1 2
      (by decide) (by decide) (by decide)
      (C (3 : K)⁻¹) (-(X 3 ^ 2 + X 3 + 1))
      (-(C (9 : K)⁻¹ * X 0))
      (-(C (9 : K)⁻¹ * X 1))
      (-(C (9 : K)⁻¹ * X 2))
    simp [p₀]
    rw [hnat3]
    linear_combination
      -(X 0 ^ 3 + X 1 ^ 3 + C (2 : K) * X 2 ^ 3) * hC9 +
      X 3 ^ 3 * hC3

end PfaffianDescent.VoisinExplicitSeparableFourLineExample
