import PfaffianDescent.CorayPerfectOriginalClosedQuinticSmallerPoint
import PfaffianDescent.CorayOriginalCubicPolynomialQuadraticSecant
import PfaffianDescent.CorayPrimeDegreeComponentOriginalSmallerPoint
import PfaffianDescent.CoraySelectedCurveOriginalClosedPoint
import PfaffianDescent.CorayCubicPolynomialDualAnnihilatorDimension

/-! SOURCE ONLY / UNVERIFIED. Connect the accepted genuine quintic
producer to the actual least-original-point reduction, retaining the SAME
original Hilbert-window n. Either the degree-four/n=2 branch remains, or
the actual selected degree-n intersection and original point are constructed
and every actual minimal component has OWN degree divisible by three.
No GI, rank, genus, regularity or desired smaller-point premise.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem originalHilbertWindow_degree_four_n_two (n : ℕ)
    (hlower : 1 + 3 * n.choose 2 ≤ 4)
    (hupper : 4 < 1 + 3 * (n + 1).choose 2) : n = 2 := by
  have hn2 : 2 ≤ n := by
    by_contra h
    have hm : (n + 1).choose 2 ≤ (2 : ℕ).choose 2 :=
      Nat.choose_le_choose 2 (by omega)
    norm_num at hm
    omega
  have hn3 : n < 3 := by
    by_contra h
    have hm : (3 : ℕ).choose 2 ≤ n.choose 2 :=
      Nat.choose_le_choose 2 (by omega)
    norm_num at hm
    omega
  omega

private theorem originalHilbertWindow_section_dimension (n : ℕ) (hn : 2 ≤ n) :
    (n + 3).choose 3 - n.choose 3 = 1 + 3 * (n + 1).choose 2 := by
  by_cases hn3 : 3 ≤ n
  · have h := cubicPolynomialAnnihilator_choose_difference (n + 1) (by omega)
    simpa only [Nat.add_assoc, Nat.reduceAdd, Nat.add_sub_cancel] using h
  · have he : n = 2 := by omega
    subst n
    decide

/-- The ORIGINAL least-coprime-point induction now consumes the actual
perfect-field degree-five construction. The SAME original n-window either
returns degree4/n2 or constructs the degree-n curve through SAME P, with
ALL genuine minimal components forced into the own-degree divisible3 case.
The component degree here is intrinsic Hilbert/hyperplane degree, not a
field degree. No genus or geometry-of-selected-member conclusion is assumed. -/
theorem perfectField_least_originalPoint_originalWindow_exists_selectedCurve_all_components_threeDivides
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (P : closedPoints (hypersurface p hp))
    (hPcop : Nat.Coprime ((hypersurfaceToBase p hp).residueDegree P.1) 3)
    (hleast : ∀ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 →
        (hypersurfaceToBase p hp).residueDegree P.1 ≤
          (hypersurfaceToBase p hp).residueDegree R.1)
    (n : ℕ)
    (hlower : 1 + 3 * n.choose 2 ≤ (hypersurfaceToBase p hp).residueDegree P.1)
    (hupper : (hypersurfaceToBase p hp).residueDegree P.1 <
      1 + 3 * (n + 1).choose 2) :
    ((hypersurfaceToBase p hp).residueDegree P.1 = 4 ∧ n = 2) ∨
      (7 ≤ (hypersurfaceToBase p hp).residueDegree P.1 ∧
        3 * n < (hypersurfaceToBase p hp).residueDegree P.1 ∧
        ∃ (q : MvPolynomial (Fin 4) K) (hq : q.IsHomogeneous n),
          q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) ∧
          ∃ Q : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)),
            cubicSecondEquationCurveImmersion p q hp n hq Q.1 = P.1 ∧
            IsIso ((cubicSecondEquationCurveImmersion p q hp n hq).residueFieldMap Q.1) ∧
            (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 =
              (hypersurfaceToBase p hp).residueDegree P.1 ∧
            ∀ C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
              C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes →
                3 ∣ actualCurveCoordinateHilbertDegree C) := by
  classical
  have hnotSmall : ¬ (hypersurfaceToBase p hp).residueDegree P.1 ≤ 2 := by
    intro hsmall
    exact hno (originalCubic_closedPoint_degree_le_two_polynomialSecant_has_section p hp P hsmall)
  have hnotThree : ¬ 3 ∣ (hypersurfaceToBase p hp).residueDegree P.1 :=
    Nat.prime_three.coprime_iff_not_dvd.mp hPcop.symm
  have hfour : 4 ≤ (hypersurfaceToBase p hp).residueDegree P.1 := by
    rw [Nat.dvd_iff_mod_eq_zero] at hnotThree
    omega
  have hnotfive : (hypersurfaceToBase p hp).residueDegree P.1 ≠ 5 := by
    intro hfive
    obtain ⟨R, hRcop, _hRbound, hRsmall⟩ :=
      perfectField_originalCubic_degree_five_closedPoint_exists_smaller_closedPoint p hp P hfive
    exact (not_lt_of_ge (hleast R hRcop)) hRsmall
  by_cases hdegreeFour : (hypersurfaceToBase p hp).residueDegree P.1 = 4
  · left
    refine ⟨hdegreeFour, originalHilbertWindow_degree_four_n_two n ?_ ?_⟩
    · simpa only [hdegreeFour] using hlower
    · simpa only [hdegreeFour] using hupper
  right
  have hnotdiv : ¬ 3 ∣ (hypersurfaceToBase p hp).residueDegree P.1 :=
    Nat.prime_three.coprime_iff_not_dvd.mp hPcop.symm
  have hlarge : 7 ≤ (hypersurfaceToBase p hp).residueDegree P.1 := by
    rw [Nat.dvd_iff_mod_eq_zero] at hnotdiv
    omega
  have hn : 2 ≤ n := by
    by_contra h
    have hm : (n + 1).choose 2 ≤ (2 : ℕ).choose 2 :=
      Nat.choose_le_choose 2 (by omega)
    norm_num at hm
    omega
  have hstrict := originalHilbertWindow_three_mul_lt n
    ((hypersurfaceToBase p hp).residueDegree P.1) hlower hupper hlarge
  rcases finite_or_infinite K with hfinite | hinfinite
  · letI : Finite K := hfinite
    exact (hno (finite_field_cubic_has_rational_section p hp)).elim
  letI : Infinite K := hinfinite
  have hsize : (hypersurfaceToBase p hp).residueDegree P.1 <
      (n + 3).choose 3 - n.choose 3 := by
    rw [originalHilbertWindow_section_dimension n hn]
    exact hupper
  obtain ⟨q, hq, hnot, Q, hpoint, hresidue, hdegree⟩ :=
    exists_selectedCurve_originalClosedPoint_of_section_dimension p hp hp0 n P hsize
  refine ⟨hlarge, hstrict, q, hq, hnot, Q, hpoint, hresidue, hdegree, ?_⟩
  intro C hCmin
  by_contra hdiv
  have hCcop : Nat.Coprime (actualCurveCoordinateHilbertDegree C) 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hdiv).symm
  obtain ⟨R, hRcop, hRsmall⟩ :=
    selectedMinimalComponent_primeDegree_exists_smaller_originalCubic_point
      p q hp hp0 n hq hnot C hCmin hCcop
      ((hypersurfaceToBase p hp).residueDegree P.1) hlower hupper hlarge
  exact (not_lt_of_ge (hleast R hRcop)) hRsmall

end PfaffianDescent.Coray
