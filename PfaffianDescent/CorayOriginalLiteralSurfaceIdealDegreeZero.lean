import PfaffianDescent.CorayWholeSurfacePlaneIdealRestrictionKernel
import PfaffianDescent.CorayWholeGenericHyperplaneRegular
import PfaffianDescent.CorayWholeIdealGradeRestriction
import Mathlib.LinearAlgebra.Dimension.Finite

/-! Literal surface ideal degree0 from original component primality. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u v
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

private theorem literalWholeIdealGrade_zero_eq_bot_of_proper
    {A : Type v} [CommRing A] [Algebra K A]
    (G : ℕ → Submodule K A) (hG : G 0 = 1)
    (J : Ideal A) (hJ : J ≠ ⊤) : wholeIdealGrade G J 0 = ⊥ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hcx⟩ := Submodule.mem_one.mp (hG ▸ hx.2)
    change x = 0
    by_cases hc : c = 0
    · subst c
      exact hcx.symm.trans (map_zero (algebraMap K A))
    · have hxUnit : IsUnit x :=
        hcx ▸ (isUnit_iff_ne_zero.mpr hc).map (algebraMap K A)
      exact False.elim (hJ (J.eq_top_of_isUnit_mem hx.1 hxUnit))
  · exact bot_le

private theorem literalQuotientWholeIdealGrade_zero_finrank_of_proper
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (J : Ideal (CoordinateRing I)) (hJ : J ≠ ⊤) :
    finrank K (wholeIdealGrade (grading I) J 0) = 0 := by
  rw [literalWholeIdealGrade_zero_eq_bot_of_proper (grading I) (grading_zero I) J hJ]
  exact finrank_bot K (CoordinateRing I)

/-- Actual original minimal-component data produce the zero initial term
of the SAME whole surface ideal. No properness/grade/rank/GI premise. -/
theorem selectedOriginalWholeCurve_literalWholeSurfaceIdealGradeZero001
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    finrank (GenericHyperplaneField K)
      (wholeIdealGrade
        (grading (equationIdeal (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)))
        (wholeOriginalSurfaceCoordinateIdeal C p hp) 0) = 0 := by
  have hpC : p ∈ C.toIdeal := by
    apply hCmin.le
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q})
  letI : (wholeGenericCurveIdeal C).toIdeal.IsPrime :=
    wholeGenericCurveIdeal_isPrime C hCmin.isPrime
  have hle : (equationIdeal
      (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)).toIdeal ≤
      (wholeGenericCurveIdeal C).toIdeal := by
    apply Ideal.span_le.mpr
    intro z hz
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact originalEquation_mem_wholeGenericCurveIdeal C p hpC
  have hPrime : (wholeOriginalSurfaceCoordinateIdeal C p hp).IsPrime := by
    change ((wholeGenericCurveIdeal C).toIdeal.map
      (Ideal.Quotient.mk (equationIdeal
        (p.map (algebraMap K (GenericHyperplaneField K))) (hp.map _)).toIdeal)).IsPrime
    exact Ideal.isPrime_map_quotientMk_of_isPrime hle
  exact literalQuotientWholeIdealGrade_zero_finrank_of_proper _ _ hPrime.ne_top

end PfaffianDescent.Coray
