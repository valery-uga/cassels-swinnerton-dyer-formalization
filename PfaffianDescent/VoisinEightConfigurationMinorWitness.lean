import PfaffianDescent.VoisinQuadraticEvaluationMatrix
import PfaffianDescent.VoisinEightFiniteAlgebraQuadraticKernel

/-!
# A full-rank quadratic minor at an actual projective configuration

The explicit split witness is retained as a field-valued point of the
ordered and unordered cubic-surface configuration spaces, together with
its eight affine-cone vectors and a unit monomial evaluation minor.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

theorem exists_generic_ordered_eight_configuration_with_quadratic_minor
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    Smooth (hypersurfaceToBase p hp) ∧
      ∃ (y : Fin 8 → Fin 4 → L)
        (hzero : ∀ i, p.eval (y i) = 0)
        (c : Fin 4 → L)
        (hc : ∀ i, (homogeneousLinearForm c).eval (y i) ≠ 0)
        (e : Fin 8 ↪ Monomials (Fin 4) 2)
        (A : Spec (.of L) ⟶
          (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
        (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
        (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8),
        Function.Surjective
          (homogeneousSectionRestriction (K := L)
            (fun j i => y i j) 2) ∧
        IsUnit (eightPointQuadraticEvaluationMinor e y).det ∧
        (∀ i, (A ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left =
            projectiveVectorSchemePointInLinearChart
              (equationIdeal p hp) c (y i)
              (cubicVector_zero_equationIdeal p hp (y i) (hzero i)) (hc i)) ∧
        A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B ∧
        B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _ ∧
        (∃ hB : B ≫ cubicConfigurationToBase p hp 8 = 𝟙 _,
          D = projectiveConfigurationFiniteSubschemeAt
            (grading (equationIdeal p hp))
            (hypersurfaceToBase p hp) 8 B hB) ∧
        Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) := by
  dsimp only
  obtain ⟨hsmooth, y, hzero, c, hc, e, A, B, D,
    hcoord, hAB, hD, hEt, _, hsurj, _, he⟩ :=
    exists_generic_eight_finite_datum_with_exact_quadratic_kernel_and_minor K φ
  obtain ⟨hB, hDfiber⟩ := hD
  exact ⟨hsmooth, y, hzero, c, hc, e, A, B, D,
    hsurj, he, hcoord, hAB, hB, ⟨hB, hDfiber⟩, hEt⟩

end PfaffianDescent
