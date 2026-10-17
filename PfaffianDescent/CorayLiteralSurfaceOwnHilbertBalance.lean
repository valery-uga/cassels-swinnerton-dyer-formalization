import PfaffianDescent.CorayWholeSurfaceIdealGradeHilbertRank
import PfaffianDescent.CorayWholeSurfacePlaneIdealRestrictionKernel
import PfaffianDescent.CorayComponentHilbertCoefficientInvariance
import PfaffianDescent.CorayCubicPolynomialDualAnnihilatorDimension

/-! Actual original-field grade balance with literal whole surface ideal. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K
set_option autoImplicit false

private lemma twice_choose_two_native (d : ℕ) : 2 * d.choose 2 = d * (d - 1) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose d 2
  rw [show Nat.factorial 2 = 2 by decide] at h
  simpa only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
    mul_one, mul_comm] using h.symm

/-- Genuine cubic Hilbert polynomial, in the exact twice-rank form needed
for ideal arithmetic. It concerns original coordinate grades, not H0. -/
theorem cubicSurfaceGrade_twice_finrank_polynomial001
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    (d : ℕ) (hd : 3 ≤ d) :
    2 * finrank K (grading (equationIdeal p hp) d) = 2 + 3 * d * (d + 1) := by
  rw [PfaffianDescent.cubicSurface_grade_finrank p hp hp0 d]
  have hchoose := cubicPolynomialAnnihilator_choose_difference (d + 1) (by omega)
  have hchoose' : (d + 3).choose 3 - d.choose 3 = 1 + 3 * (d + 1).choose 2 := by
    simpa only [Nat.add_assoc, Nat.add_sub_cancel] using hchoose
  rw [hchoose']
  have htwo := twice_choose_two_native (d + 1)
  simp only [Nat.add_sub_cancel] at htwo
  nlinarith

/-- SAME original C grades and SAME whole surface ideal satisfy genuine
rank-nullity. The original-field C rank is identified by actual coefficient
extension; no Hilbert or ideal rank certificate is supplied. -/
theorem selectedOriginalWholeCurve_grade_finrank_add_literalSurfaceIdealGrade001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal PS)
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (d : ℕ) :
    finrank K (grading C d) +
      finrank (GenericHyperplaneField K) (wholeIdealGrade
        (grading (equationIdeal (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)))
        (wholeOriginalSurfaceCoordinateIdeal C p hp) d) =
        finrank (GenericHyperplaneField K)
          (grading (equationIdeal (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)) d) := by
  have hpC : p ∈ C.toIdeal := by
    apply hCmin.le
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q})
  let F := GenericHyperplaneField K
  let I := equationIdeal (p.map (algebraMap K F)) (hp.map _)
  let J := wholeGenericCurveIdeal C
  have hIJ : I.toIdeal ≤ J.toIdeal := by
    apply Ideal.span_le.mpr
    rintro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact originalEquation_mem_wholeGenericCurveIdeal C p hpC
  have h := homogeneousQuotientGrade_finrank_add_wholeIdealGrade I J hIJ d
  have hbase := actualComponentGrade_finrank_eq_coefficientExtension C J
    (wholeGenericCurveIdeal_toIdeal C).symm d
  rw [hbase] at h
  exact h

end PfaffianDescent.Coray
