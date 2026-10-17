import PfaffianDescent.CorayWholeGenericHyperplaneRegular
import PfaffianDescent.CorayOwnMinimalComponentDegreePositiveAnyField
import PfaffianDescent.CorayComponentHilbertCoefficientInvariance

/-! SOURCE ONLY / UNVERIFIED152. Actual generic-H regularity and original
whole-curve Hilbert increments construct finiteness and rank=m for the SAME
literal whole C_L+(H). No generic-cut finite/regular/degree certificate enters
the actual original-p/q caller. Constants rank r_C is not altered. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial AlgebraicGeometry Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every-degree Hilbert equality for the literal whole parameter extension. -/
theorem wholeGenericCurveGrade_finrank_eq
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (d : ℕ) :
    finrank (GenericHyperplaneField K) (grading (wholeGenericCurveIdeal C) d) =
      finrank K (grading C d) :=
  actualComponentGrade_finrank_eq_coefficientExtension C (wholeGenericCurveIdeal C)
    (wholeGenericCurveIdeal_toIdeal C).symm d

/-- Conversion helper: an ORIGINAL whole-curve increment plus derived actual
H regularity gives exact eventual grades of this SAME whole generic cut.
No section regularity/finiteness or cut Hilbert premise is supplied. -/
theorem wholeGenericCut_eventualHilbert_eq_original_degree
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (hprime : C.toIdeal.IsPrime)
    (P : scheme C) (N : ℕ)
    (hN : ∀ d, N ≤ d → finrank K (grading C (d + 1)) =
      finrank K (grading C d) + actualCurveCoordinateHilbertDegree C) :
    ∀ d, N + 1 ≤ d →
      finrank (GenericHyperplaneField K) (grading (wholeGenericCutIdeal C) d) =
        actualCurveCoordinateHilbertDegree C := by
  letI : (wholeGenericCurveIdeal C).toIdeal.IsPrime := wholeGenericCurveIdeal_isPrime C hprime
  intro d hd
  have hindex : d - 1 + 1 = d := by omega
  have hstep := componentLinearGrade_hilbertFunction_recurrence
    (wholeGenericCurveIdeal C) (genericHyperplaneEquation (K := K))
    genericHyperplaneEquation_isHomogeneous (wholeGenericHyperplane_not_mem C hprime P) (d - 1)
  change finrank (GenericHyperplaneField K) (grading (wholeGenericCurveIdeal C) (d - 1 + 1)) =
    finrank (GenericHyperplaneField K) (grading (wholeGenericCurveIdeal C) (d - 1)) +
      finrank (GenericHyperplaneField K) (grading (wholeGenericCutIdeal C) (d - 1 + 1)) at hstep
  rw [hindex, wholeGenericCurveGrade_finrank_eq, wholeGenericCurveGrade_finrank_eq] at hstep
  have horig := hN (d - 1) (by omega)
  rw [hindex] at horig
  omega

/-- The ACTUAL original selected C constructs the finite generic whole cut,
its true native rank m, and its actual native regular-principal immersion.
No prime/point/regularity/finiteness/degree conclusion after extension is an input.
The original coordinate Hilbert degree is retained verbatim. -/
theorem selectedOriginalWholeCurve_genericCut_finite_rank_degree
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    ∃ hfinite : IsFinite (toBase (wholeGenericCutIdeal C)),
      letI := hfinite
      finiteSchemeRank (toBase (wholeGenericCutIdeal C)) = actualCurveCoordinateHilbertDegree C ∧
        Nonempty (PfaffianDescent.RegularPrincipalImmersion
          (PfaffianDescent.schemeQuotientMap (wholeGenericCurveIdeal C)
            (wholeGenericCutIdeal C) le_sup_left)) ∧
        ∃ N, ∀ d, N ≤ d →
          finrank (GenericHyperplaneField K) (grading (wholeGenericCutIdeal C) d) =
            actualCurveCoordinateHilbertDegree C := by
  classical
  have hrel := selectedProjectiveMinimalComponent_homogeneous_relevant
    p q hp hp0 n hq hnot C hCmin
  let P := homogeneousPrimeQuotientProjectivePoint C hCmin.isPrime hrel
  obtain ⟨_hpos, _hbound, N, hN⟩ :=
    selectedProjectiveMinimalComponent_hilbertDegree_pos_bound_and_eventualIncrement_anyField
      p q hp hp0 n hq hnot C hCmin
  have hgrades := wholeGenericCut_eventualHilbert_eq_original_degree C hCmin.isPrime P N hN
  have hfinite : IsFinite (toBase (wholeGenericCutIdeal C)) :=
    PfaffianDescent.projective_finite_of_hilbert_bound (wholeGenericCutIdeal C)
      (N + 1) (actualCurveCoordinateHilbertDegree C) (fun d hd => (hgrades d hd).le)
  letI := hfinite
  obtain ⟨M, hM⟩ := finiteProjectiveHomogeneousIdeal_hilbertFunction_eventually_eq_rank_anyField
    (wholeGenericCutIdeal C)
  have hrank : finiteSchemeRank (toBase (wholeGenericCutIdeal C)) =
      actualCurveCoordinateHilbertDegree C :=
    (hM (max M (N + 1)) (le_max_left _ _)).symm.trans
      (hgrades (max M (N + 1)) (le_max_right _ _))
  exact ⟨hfinite, hrank, ⟨wholeGenericHyperplane_regularPrincipalImmersion C hCmin.isPrime P⟩,
    N + 1, hgrades⟩

end PfaffianDescent.Coray
