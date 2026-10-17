import PfaffianDescent.CorayOriginalLeastPointNonintegralBClosure
import PfaffianDescent.CorayPerfectMinimalOriginalPointComponentFrontier
import PfaffianDescent.CorayAllSelectedAiiClosure
import PfaffianDescent.CorayIntegralAiiiProducerClosure
import PfaffianDescent.CorayCubicPolynomialDualAnnihilatorDimension

/-! Natural least-point case reduction after actual B and A(ii)/A(iii).
The minimum-degree A(i) pencil/image construction remains an explicit gap. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The primitive ORIGINAL boundary constructor supplies a nonintegral
SAME q after integral A(iii), and actual B contradicts leastness. No selected
q, singular cycle, component, GI or smaller-point outcome is supplied. -/
theorem coray_largeBoundary_through_least_originalCubic_point_false001
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPointCoprime : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (m : ℕ) (hm : 3 ≤ m)
    (hdegree : (hypersurfaceToBase p hp).residueDegree P.1 =
      (m + 3).choose 3 - m.choose 3) : False := by
  obtain ⟨q, hq, hnot, hPcurve, hNonIntegral⟩ :=
    boundary_least_originalPoint_exists_nonintegral_selectedCurve
      p hp hp0 P hPointCoprime hleast hno m hm hdegree
  have hCount : (m + 3).choose 3 - m.choose 3 = 1 + 3 * (m + 1).choose 2 := by
    have h := cubicPolynomialAnnihilator_choose_difference (m + 1) (by omega)
    simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.add_sub_cancel] using h
  have hNatDegree : (hypersurfaceToBase p hp).residueDegree P.1 =
      1 + 3 * (m + 1).choose 2 := hdegree.trans hCount
  have hStep : ((m + 1) + 1).choose 2 = (m + 1) + (m + 1).choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ' (m + 1) 1
  have hUpper : (hypersurfaceToBase p hp).residueDegree P.1 <
      1 + 3 * ((m + 1) + 1).choose 2 := by
    rw [hNatDegree, hStep]
    omega
  have hLarge : 7 ≤ (hypersurfaceToBase p hp).residueDegree P.1 := by
    have hChoose : (3 : ℕ).choose 2 ≤ (m + 1).choose 2 :=
      Nat.choose_le_choose 2 (by omega)
    norm_num at hChoose
    rw [hNatDegree]
    omega
  exact coray_case_B_nonintegral_selectedCurve_through_least_originalCubic_point_false001
    p q hp hp0 (m + 1) (by omega) hq hnot P hPointCoprime hleast hPcurve
    hNatDegree.ge hUpper hLarge hNonIntegral

/-- Natural ORIGINAL least-point window is degree4/n2, degree10/n3, or
strict A(i) with freedom>=4 and actual through-point dimension>=5. In that
residual family EVERY newly chosen SAME-degree q through P is integral,
proved by actual B. No integral-family, minimum-degree/image or GI outcome
is an input. This is a remaining-case reduction, not full Coray. -/
theorem coray_leastOriginalPoint_window_eq_four_or_ten_or_strict_integral_family001
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (P : closedPoints (hypersurface p hp))
    (hPointCoprime : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤ (hypersurfaceToBase p hp).residueDegree R.1)
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (n : ℕ)
    (hLower : 1 + 3 * n.choose 2 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hUpper : (hypersurfaceToBase p hp).residueDegree P.1 < 1 + 3 * (n + 1).choose 2) :
    ((hypersurfaceToBase p hp).residueDegree P.1 = 4 ∧ n = 2) ∨
      ((hypersurfaceToBase p hp).residueDegree P.1 = 10 ∧ n = 3) ∨
      (3 ≤ n ∧ 7 ≤ (hypersurfaceToBase p hp).residueDegree P.1 ∧
        1 + 3 * n.choose 2 < (hypersurfaceToBase p hp).residueDegree P.1 ∧
        4 ≤ 3 * (n + 1).choose 2 - (hypersurfaceToBase p hp).residueDegree P.1 ∧
        (hypersurfaceToBase p hp).residueDegree P.1 + 5 ≤ (n + 3).choose 3 - n.choose 3 ∧
        (∀ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
          q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) →
          P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp n hq) →
          IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))) ∧
        ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
          q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
          P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp n hq)) := by
  classical
  rcases perfectField_least_originalPoint_originalWindow_exists_selectedCurve_all_components_threeDivides
      p hp hp0 hno P hPointCoprime hleast n hLower hUpper with hFour | hLarge
  · exact Or.inl hFour
  rcases hLarge with ⟨hPointLarge, hThreeN, q, hq, hnot, PX, hPXpoint, hPXiso, hPXdegree, hAllThree⟩
  have hnTwo : 2 ≤ n := by
    by_contra h
    have hChoose : (n + 1).choose 2 ≤ (2 : ℕ).choose 2 := Nat.choose_le_choose 2 (by omega)
    norm_num at hChoose
    omega
  have hPcurve : P.1 ∈ Set.range (cubicSecondEquationCurveImmersion p q hp n hq) := ⟨PX.1, hPXpoint⟩
  by_cases hBoundary : (hypersurfaceToBase p hp).residueDegree P.1 = 1 + 3 * n.choose 2
  · by_cases hnThree : n = 3
    · right
      left
      refine ⟨?_, hnThree⟩
      have hEq := hBoundary
      rw [hnThree] at hEq
      norm_num at hEq
      exact hEq
    have hnNotTwo : n ≠ 2 := by
      intro hnEq
      have hEq := hBoundary
      rw [hnEq] at hEq
      norm_num at hEq
      omega
    have hnFour : 4 ≤ n := by omega
    have hCount : ((n - 1) + 3).choose 3 - (n - 1).choose 3 = 1 + 3 * n.choose 2 := by
      rw [show n - 1 + 3 = n + 2 by omega]
      exact cubicPolynomialAnnihilator_choose_difference n hnFour
    exact False.elim (coray_largeBoundary_through_least_originalCubic_point_false001
      p hp hp0 P hPointCoprime hleast hno (n - 1) (by omega) (hBoundary.trans hCount.symm))
  right
  right
  have hStrict : 1 + 3 * n.choose 2 < (hypersurfaceToBase p hp).residueDegree P.1 := by omega
  have hFreedomThree : 3 ≤ 3 * (n + 1).choose 2 - (hypersurfaceToBase p hp).residueDegree P.1 := by
    by_contra h
    exact coray_case_Aii_selectedCurve_through_least_originalCubic_point_false
      p q hp hp0 n hnTwo hq hnot P hPointCoprime hleast hPcurve (by omega) (by omega)
  have hPointNotThree := Nat.prime_three.coprime_iff_not_dvd.mp hPointCoprime.symm
  have hFreedom : 4 ≤ 3 * (n + 1).choose 2 - (hypersurfaceToBase p hp).residueDegree P.1 := by
    rw [Nat.dvd_iff_mod_eq_zero] at hPointNotThree
    omega
  have hnThree : 3 ≤ n := by
    by_contra h
    have hChoose : (n + 1).choose 2 ≤ (3 : ℕ).choose 2 := Nat.choose_le_choose 2 (by omega)
    norm_num at hChoose
    omega
  have hCount : (n + 3).choose 3 - n.choose 3 = 1 + 3 * (n + 1).choose 2 := by
    have h := cubicPolynomialAnnihilator_choose_difference (n + 1) (by omega)
    simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.add_sub_cancel] using h
  have hSize : (hypersurfaceToBase p hp).residueDegree P.1 + 5 ≤ (n + 3).choose 3 - n.choose 3 := by
    rw [hCount]
    omega
  refine ⟨hnThree, hPointLarge, hStrict, hFreedom, hSize, ?_, q, hq, hnot, hPcurve⟩
  intro q0 hq0 hnot0 hPcurve0
  by_contra hNonIntegral
  exact coray_case_B_nonintegral_selectedCurve_through_least_originalCubic_point_false001
    p q0 hp hp0 n (by omega) hq0 hnot0 P hPointCoprime hleast hPcurve0 hLower hUpper hPointLarge hNonIntegral

end PfaffianDescent.Coray
