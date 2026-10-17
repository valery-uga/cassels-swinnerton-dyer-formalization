import PfaffianDescent.CorayCanonicalSurfaceIdealNumericalIncrement
import PfaffianDescent.CorayOriginalLiteralSurfaceIdealDegreeZero
import PfaffianDescent.CorayWholeIdealIncrementArithmetic

/-! Genuine original-input telescoping, including internally constructed grade0. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
/-- The SAME original component's actual surface ideal Hilbert function
satisfies the quadratic bound. No initial rank or recurrence outcome input. -/
theorem charZero_selectedOriginalWholeCurve_surfaceIdealGrade_twice_quadraticBound001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (lambda : ℕ) (hMu : actualCurveCoordinateHilbertDegree C = 3 * lambda)
    (s : ℕ) :
    2 * Module.finrank (GenericHyperplaneField K)
      (wholeOriginalSurfaceIdealGrade C p hp (lambda + s)) ≤ 2 + 3 * s * (s + 1) := by
  let a : ℕ → ℕ := fun d => Module.finrank (GenericHyperplaneField K)
    (wholeOriginalSurfaceIdealGrade C p hp d)
  have hZero : a 0 = 0 :=
    selectedOriginalWholeCurve_literalWholeSurfaceIdealGradeZero001
      p q hp hp0 n hq hnot C hCmin
  have hStep : ∀ d, a (d + 1) ≤ a d +
      (if 3 * (d + 1) = 3 * lambda then 1 else 3 * (d + 1) - 3 * lambda) :=
    charZero_selectedOriginalWholeCurve_surfaceIdealGrade_numericalIncrement001
      p q hp hp0 n hq hnot C hCmin lambda hMu
  exact idealGrade_twice_le_quadratic_above_third_degree a lambda hZero hStep s

end PfaffianDescent.Coray
