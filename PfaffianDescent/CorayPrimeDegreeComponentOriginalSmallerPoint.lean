import PfaffianDescent.CorayActualComponentHyperplaneCartierDegree
import PfaffianDescent.CoraySelectedComponentHeightAndRelevance
import PfaffianDescent.CorayEffectiveCyclePointBound
import PfaffianDescent.CorayHomogeneousComponentOriginalClosedPoint
import PfaffianDescent.CorayCubicSecondEquationActualCurveUnit
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega

/-! Source-only / unverified. The actual ORIGINAL-K component hyperplane
cycle produces a smaller original cubic point when that SAME component's
intrinsic degree is prime to three. No cycle, finite hyperplane, genus,
regularity or desired smaller-point premise is supplied. The original
Hilbert window derives the strict degree bound. The remaining own-degree
multiple-of-three case is explicit, not claimed solved. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The elementary estimate needed for the ORIGINAL lower Hilbert window. -/
theorem originalHilbertWindow_chooseTwo_ge_self (n : ℕ) (hn : 3 ≤ n) :
    n ≤ n.choose 2 := by
  have hstep : ∀ k : ℕ, k + 3 ≤ (k + 3).choose 2 := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      have hrec : ((k + 3) + 1).choose 2 = (k + 3) + (k + 3).choose 2 :=
        (Nat.choose_succ_succ' (k + 3) 1).trans
          (congrArg (fun a : ℕ => a + (k + 3).choose 2)
            (Nat.choose_one_right (k + 3)))
      have hle : k + 1 + 3 ≤ (k + 3) + (k + 3).choose 2 := by omega
      calc
        k + 1 + 3 ≤ (k + 3) + (k + 3).choose 2 := hle
        _ = ((k + 3) + 1).choose 2 := hrec.symm
        _ = (k + 1 + 3).choose 2 :=
          congrArg (fun a : ℕ => a.choose 2) (by omega)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hnk : n = k + 3 := by omega
  rw [hnk]
  exact hstep k

/-- For n≥3, the actual lower window H_(n−1)≤d already gives3n<d. -/
theorem originalHilbertWindow_three_mul_lt_of_large_n (n d : ℕ) (hn : 3 ≤ n)
    (hlower : 1 + 3 * n.choose 2 ≤ d) : 3 * n < d := by
  have hchoose := originalHilbertWindow_chooseTwo_ge_self n hn
  omega

/-- The full ORIGINAL window gives3n<d for d≥7. The n=2 branch is6<d;
n≤1 is excluded by the upper window. This does not assert the d=5 case. -/
theorem originalHilbertWindow_three_mul_lt (n d : ℕ)
    (hlower : 1 + 3 * n.choose 2 ≤ d)
    (hupper : d < 1 + 3 * (n + 1).choose 2) (hlarge : 7 ≤ d) :
    3 * n < d := by
  by_cases hn : 3 ≤ n
  · exact originalHilbertWindow_three_mul_lt_of_large_n n d hn hlower
  · have hn2 : 2 ≤ n := by
      by_contra h
      have hm : (n + 1).choose 2 ≤ (2 : ℕ).choose 2 :=
        Nat.choose_le_choose 2 (by omega)
      norm_num at hm
      omega
    have hnEq : n = 2 := by omega
    subst n
    omega

section
variable {K : Type u} [Field K] [Infinite K]

/-- Construct the OWN hyperplane Cartier cycle of an ACTUAL minimal
component of the ORIGINAL p/q intersection, then extract an actual point
on its original cubic image. Its original-K degree is bounded by the OWN
component degree, which is internally derived ≤3n. -/
theorem selectedMinimalComponent_primeDegree_exists_originalCubic_point_bound
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hcop : Nat.Coprime (actualCurveCoordinateHilbertDegree C) 3) :
    ∃ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
      (hypersurfaceToBase p hp).residueDegree R.1 ≤ actualCurveCoordinateHilbertDegree C ∧
      actualCurveCoordinateHilbertDegree C ≤ 3 * n := by
  classical
  letI : C.toIdeal.IsPrime := hCmin.isPrime
  have hCrel := selectedProjectiveMinimalComponent_homogeneous_relevant
    p q hp hp0 n hq hnot C hCmin
  obtain ⟨H, hH, hnotC, hfinite, _hregular, zS, hdegree, hbound⟩ :=
    selectedProjectiveRelevantPrime_exists_hyperplaneCartierCycle_degree
      p q hp hp0 n hq hnot C hCrel hCmin.le
  let S := C ⊔ equationIdeal H hH
  letI : IsFinite (toBase S) := hfinite
  let iH := PfaffianDescent.schemeQuotientMap C S le_sup_left
  letI : IsClosedImmersion iH :=
    PfaffianDescent.schemeQuotientMap_closedImmersion C S le_sup_left
  let zC : EffectiveZeroCycle (scheme C) := pushforwardClosedCycle iH zS
  have hzC : EffectiveZeroCycle.degree (toBase C) zC =
      actualCurveCoordinateHilbertDegree C := hdegree
  have hPC : (equationIdeal p hp).toIdeal ≤ C.toIdeal :=
    (show (equationIdeal p hp).toIdeal ≤
      (projectiveIntersectionIdeal p q hp hq).toIdeal from le_sup_left).trans hCmin.le
  let iC := PfaffianDescent.schemeQuotientMap (equationIdeal p hp) C hPC
  letI : IsClosedImmersion iC :=
    PfaffianDescent.schemeQuotientMap_closedImmersion (equationIdeal p hp) C hPC
  have hbase : iC ≫ hypersurfaceToBase p hp = toBase C :=
    PfaffianDescent.schemeQuotientMap_toBase (equationIdeal p hp) C hPC
  have hcycleCop : Nat.Coprime
      (EffectiveZeroCycle.degree (iC ≫ hypersurfaceToBase p hp) zC) 3 := by
    rw [hbase, hzC]
    exact hcop
  obtain ⟨Q, hQcop, hQbound⟩ :=
    proper_effectiveCycle_coprime_degree_has_bounded_imagePoint
      iC (hypersurfaceToBase p hp) zC hcycleCop
  rw [hbase, hzC] at hQbound
  letI : UniversallyClosed iC := inferInstance
  let R : closedPoints (scheme (equationIdeal p hp)) :=
    @universallyClosedPointMap (scheme C) (scheme (equationIdeal p hp))
      iC (inferInstance : UniversallyClosed iC) Q
  exact ⟨R, hQcop, hQbound, hbound⟩

/-- The natural prime-to-three OWN component degree case yields a smaller
point from the ORIGINAL d/n window;3n<d is proved, never supplied. -/
theorem selectedMinimalComponent_primeDegree_exists_smaller_originalCubic_point
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (hcop : Nat.Coprime (actualCurveCoordinateHilbertDegree C) 3)
    (d : ℕ) (hlower : 1 + 3 * n.choose 2 ≤ d)
    (hupper : d < 1 + 3 * (n + 1).choose 2) (hlarge : 7 ≤ d) :
    ∃ R : closedPoints (hypersurface p hp),
      Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
      (hypersurfaceToBase p hp).residueDegree R.1 < d := by
  obtain ⟨R, hRcop, hRbound, hCbound⟩ :=
    selectedMinimalComponent_primeDegree_exists_originalCubic_point_bound
      p q hp hp0 n hq hnot C hCmin hcop
  exact ⟨R, hRcop, hRbound.trans_lt
    (hCbound.trans_lt (originalHilbertWindow_three_mul_lt n d hlower hupper hlarge))⟩

/-- Starting from the literal selected intersection's SAME original point,
construct a minimal component carrying it and preserve its original residue
degree. Then either that OWN component degree is divisible by3, or its
constructed hyperplane cycle gives a smaller ORIGINAL cubic point.
The first disjunct is the remaining branch-B obligation, not a conclusion
of the full Coray theorem. No normalization/genus/cycle premise is added. -/
theorem originalIntersectionPoint_exists_component_threeDivides_or_smaller_originalCubic_point
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hlower : 1 + 3 * n.choose 2 ≤ (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1)
    (hupper : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 <
      1 + 3 * (n + 1).choose 2)
    (hlarge : 7 ≤ (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1) :
    ∃ (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
      (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal),
      C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes ∧
      C.toIdeal.IsPrime ∧ ∃ Q : closedPoints (scheme C),
        PfaffianDescent.schemeQuotientMap (projectiveIntersectionIdeal p q hp hq) C hIC Q.1 = P.1 ∧
        (toBase C).residueDegree Q.1 =
          (hypersurfaceToBase p hp).residueDegree (cubicSecondEquationCurveImmersion p q hp n hq P.1) ∧
        (3 ∣ actualCurveCoordinateHilbertDegree C ∨
          ∃ R : closedPoints (hypersurface p hp),
            Nat.Coprime ((hypersurfaceToBase p hp).residueDegree R.1) 3 ∧
            (hypersurfaceToBase p hp).residueDegree R.1 <
              (hypersurfaceToBase p hp).residueDegree
                (cubicSecondEquationCurveImmersion p q hp n hq P.1)) := by
  classical
  obtain ⟨C, hIC, hCmin, hCprime, Q, hpoint, _hiso, hdegree⟩ :=
    homogeneousProjective_originalClosedPoint_exists_minimalComponent
      (projectiveIntersectionIdeal p q hp hq) P
  let i := cubicSecondEquationCurveImmersion p q hp n hq
  letI : IsIso (i.residueFieldMap P.1) :=
    isIso_residueFieldMap_of_surjectiveOnStalks i P.1
  have hOriginalDegree := residueDegree_comp_of_residueFieldMap_isIso
    i (hypersurfaceToBase p hp) P.1
  rw [cubicSecondEquationCurveImmersion_toBase] at hOriginalDegree
  refine ⟨C, hIC, hCmin, hCprime, Q, hpoint, hdegree.trans hOriginalDegree, ?_⟩
  by_cases hdiv : 3 ∣ actualCurveCoordinateHilbertDegree C
  · exact Or.inl hdiv
  · right
    have hcop : Nat.Coprime (actualCurveCoordinateHilbertDegree C) 3 :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hdiv).symm
    obtain ⟨R, hRcop, hRlt⟩ :=
      selectedMinimalComponent_primeDegree_exists_smaller_originalCubic_point
        p q hp hp0 n hq hnot C hCmin hcop
        ((toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1)
        hlower hupper hlarge
    exact ⟨R, hRcop, hRlt.trans_eq hOriginalDegree⟩

end
end PfaffianDescent.Coray
end
