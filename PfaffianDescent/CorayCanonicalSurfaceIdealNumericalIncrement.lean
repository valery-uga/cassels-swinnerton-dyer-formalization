import PfaffianDescent.CorayOriginalWholeIdealGradeRecurrence
import PfaffianDescent.CorayCanonicalPlaneWholeThreeWindowIdealGradeBound

/-! Every original surface increment is constructed from SAME canonical whole cut. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
/-- Original geometry internally supplies the literal surface recurrence
and all plane coefficient bounds; neither is a premise. -/
theorem charZero_selectedOriginalWholeCurve_surfaceIdealGrade_numericalIncrement001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (lambda : ℕ) (hMu : actualCurveCoordinateHilbertDegree C = 3 * lambda)
    (d : ℕ) :
    Module.finrank (GenericHyperplaneField K) (wholeOriginalSurfaceIdealGrade C p hp (d + 1)) ≤
      Module.finrank (GenericHyperplaneField K) (wholeOriginalSurfaceIdealGrade C p hp d) +
        (if 3 * (d + 1) = 3 * lambda then 1 else 3 * (d + 1) - 3 * lambda) := by
  have hRecurrence := selectedOriginalWholeCurve_wholeIdealGrade_finrank_recurrence_le
    p q hp hp0 n hq hnot C hCmin d
  have hPlane := charZero_selectedOriginalWholeCurve_canonicalPlane_threeWindow_idealGradeBound001
    p q hp hp0 n hq hnot C hCmin lambda hMu (d + 1) (by omega)
  exact hRecurrence.trans (Nat.add_le_add_left hPlane _)

end PfaffianDescent.Coray
