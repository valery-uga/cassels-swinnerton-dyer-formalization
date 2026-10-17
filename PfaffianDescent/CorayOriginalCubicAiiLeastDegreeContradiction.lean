import PfaffianDescent.CoraySelectedCurveOriginalPointIncidenceLift
import PfaffianDescent.CorayActualSignedWordOriginalCubicSmallerPoint
import PfaffianDescent.CorayMinimalPointSelection

/-! Actual least-degree contradictions on the SAME ORIGINAL cubic. The
selected q's genuine GI and original-point incidence remain explicit.
The actual closed curve lift, its residue preservation, the signed word,
nonzero section, own native-length cycle and smaller original point are
all constructed. No smaller point/cycle/word/section premise. SOURCE ONLY /
UNVERIFIED. GI selection/reducible branch are separate geometry. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace AllCharacteristics
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine GI selected curve through the SAME least prime-to-three
ORIGINAL cubic point cannot lie in A(ii), n≥3, with the natural original
degree/freedom constraints. The smaller point is actually constructed. -/
theorem coray_case_Aii_geometricallyIntegral_selectedCurve_through_least_originalCubic_point_false
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hlarge : 3 ≤ n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤
          (hypersurfaceToBase p hp).residueDegree R.1)
    (hPcurve : P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp n hq))
    (hdegree : (hypersurfaceToBase p hp).residueDegree P.1 ≤ 3 * (n + 1).choose 2)
    (hfreedom : 3 * (n + 1).choose 2 -
      (hypersurfaceToBase p hp).residueDegree P.1 < 3) : False := by
  obtain ⟨Q, hpoint, _hresidue, hQdegree⟩ :=
    selectedCurve_originalClosedPoint_of_originalPoint_mem_image p q hp n hq P hPcurve
  have hprimeQ : ¬ 3 ∣ (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 := by
    rw [hQdegree]
    exact Nat.prime_three.coprime_iff_not_dvd.mp hPcop.symm
  have hdegreeQ : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 ≤
      3 * (n + 1).choose 2 := by
    rw [hQdegree]
    exact hdegree
  have hfreedomQ : 3 * (n + 1).choose 2 -
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 < 3 := by
    rw [hQdegree]
    exact hfreedom
  obtain ⟨R, hRcop, hRsmall⟩ :=
    coray_case_Aii_geometricallyIntegral_originalPoint_exists_smaller_originalCubic_closedPoint
      p q hp hp0 n hlarge hq hnot Q hprimeQ hdegreeQ hfreedomQ
  rw [hpoint] at hRsmall
  exact (not_lt_of_ge (hleast R hRcop)) hRsmall

/-- The SAME ORIGINAL cubic least-degree premise also excludes the actual
GI n=2 A(ii) cases degree7/8. The actual smaller point has degree at most4;
the contradiction uses only its derived coprimality and strict inequality. -/
theorem coray_case_Aii_degree_seven_eight_geometricallyIntegral_selectedCurve_through_least_originalCubic_point_false
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (hq : q.IsHomogeneous 2)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (hypersurface p hp))
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤
          (hypersurfaceToBase p hp).residueDegree R.1)
    (hPcurve : P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp 2 hq))
    (hdegrees : (hypersurfaceToBase p hp).residueDegree P.1 = 7 ∨
      (hypersurfaceToBase p hp).residueDegree P.1 = 8) : False := by
  obtain ⟨Q, hpoint, _hresidue, hQdegree⟩ :=
    selectedCurve_originalClosedPoint_of_originalPoint_mem_image p q hp 2 hq P hPcurve
  have hdegreesQ : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 = 7 ∨
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 = 8 := by
    rw [hQdegree]
    exact hdegrees
  obtain ⟨R, hRcop, _hRfour, hRsmall⟩ :=
    coray_case_Aii_degree_seven_eight_geometricallyIntegral_originalPoint_exists_smaller_originalCubic_closedPoint
      p q hp hp0 hq hnot Q hdegreesQ
  rw [hpoint] at hRsmall
  exact (not_lt_of_ge (hleast R hRcop)) hRsmall

end PfaffianDescent.Coray
