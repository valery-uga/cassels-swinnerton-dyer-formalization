import PfaffianDescent.CorayLiteralSurfaceOwnHilbertBalance
import PfaffianDescent.CorayCanonicalSurfaceIdealQuadraticBound
import PfaffianDescent.CorayOriginalWholeIdealGradeRecurrence

/-! SAME original coordinate Hilbert lower bound from genuine canonical telescoping. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- In the genuine degree=3r branch, whole ideal increments derive the
OWN original-coordinate Hilbert lower bound. The zero-Euler increment of
one is retained, so the resulting Euler constant has its correct value. -/
theorem selectedOriginalWholeCurve_ownGrade_twice_finrank_lower_bound001
    [CharZero K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal PS)
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (r d : ℕ) (hdegree : actualCurveCoordinateHilbertDegree C = 3 * r)
    (hrd : r ≤ d) (hd : 3 ≤ d) :
    6 * r * d ≤ 2 * finrank K (grading C d) + 3 * r * (r - 1) := by
  let a : ℕ → ℕ := fun t => finrank (GenericHyperplaneField K)
    (wholeOriginalSurfaceIdealGrade C p hp t)
  have hpF0 : p.map (algebraMap K (GenericHyperplaneField K)) ≠ 0 := by
    intro hz
    apply hp0
    apply MvPolynomial.map_injective _ (algebraMap K (GenericHyperplaneField K)).injective
    simpa only [map_zero] using hz
  have hadd := selectedOriginalWholeCurve_grade_finrank_add_literalSurfaceIdealGrade001
    p q hp hp0 n hq hnot C hCmin d
  have hsurface := cubicSurfaceGrade_twice_finrank_polynomial001
    (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _) hpF0 d hd
  by_cases hr0 : r = 0
  · subst r; simp
  · obtain ⟨s, hs⟩ := Nat.exists_eq_add_of_le hrd
    have hideal := charZero_selectedOriginalWholeCurve_surfaceIdealGrade_twice_quadraticBound001
      p q hp hp0 n hq hnot C hCmin r hdegree s
    rw [← hs] at hideal
    have hrpred : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr0)
    change finrank K (grading C d) + a d = _ at hadd
    have hrprod : r * (r - 1) + r = r * r := by
      calc
        _ = r * (r - 1 + 1) := by ring
        _ = r * r := by rw [hrpred]
    have hbalance : 3 * d * (d + 1) + 3 * r * (r - 1) =
        3 * s * (s + 1) + 6 * r * d := by
      rw [hs]
      nlinarith [hrprod]
    nlinarith [hbalance]

end PfaffianDescent.Coray
