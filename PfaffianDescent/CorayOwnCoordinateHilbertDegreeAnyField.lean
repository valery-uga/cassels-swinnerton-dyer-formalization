import PfaffianDescent.CorayOriginalFieldHilbertIncrementBound
import PfaffianDescent.CorayOwnCoordinateCartierCut
import PfaffianDescent.CorayFiniteProjectiveHilbertStabilizationAnyField

/-! SOURCE ONLY / UNVERIFIED; blocked until genuine whole finite-projective
stabilization129 is accepted. SAME original C/P coordinate cut, actual grade
recurrence, and whole-pair bound. No Infinite/Perfect/GI/genus premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A genuine prime's literal whole finite linear cut realizes its intrinsic
degree over ANY field. The multiplication sequence is the actual grade map. -/
theorem primeComponent_linearSection_degree_and_eventualIncrement_anyField
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [C.toIdeal.IsPrime]
    (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1) (hnot : H ∉ C.toIdeal)
    [IsFinite (toBase (C ⊔ equationIdeal H hH))] :
    actualCurveCoordinateHilbertDegree C = finiteSchemeRank (toBase (C ⊔ equationIdeal H hH)) ∧
      ∃ N : ℕ, ∀ m, N ≤ m →
        finrank K (grading C (m + 1)) = finrank K (grading C m) +
          finiteSchemeRank (toBase (C ⊔ equationIdeal H hH)) := by
  obtain ⟨N, hN⟩ := finiteProjectiveHomogeneousIdeal_hilbertFunction_eventually_eq_rank_anyField
    (C ⊔ equationIdeal H hH)
  have hincrement : ∀ m, N ≤ m →
      finrank K (grading C (m + 1)) = finrank K (grading C m) +
        finiteSchemeRank (toBase (C ⊔ equationIdeal H hH)) := by
    intro m hm
    have hstep := componentLinearGrade_hilbertFunction_recurrence C H hH hnot m
    rw [hN (m + 1) (by omega)] at hstep
    exact hstep
  exact ⟨actualCoordinateDegree_eq_eventualIncrement_anyField C _ N hincrement,
    N, hincrement⟩

/-- Original equations and SAME P construct the coordinate cut, its native
finite rank, the OWN intrinsic degree and actual increment, bounded by3n.
Nilpotents, original residue degrees and full original field are retained. -/
theorem selectedProjectivePrimeComponent_exists_coordinateCartierCut_degree_bound_anyField
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (hprime : C.toIdeal.IsPrime) (P : scheme C) :
    ∃ j : Fin 4, coordinate C j ∉ P.asHomogeneousIdeal ∧
      MvPolynomial.X j ∉ C.toIdeal ∧
      ∃ hfinite : IsFinite (toBase
        (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))),
        letI := hfinite
        Nonempty (PfaffianDescent.RegularPrincipalImmersion (PfaffianDescent.schemeQuotientMap C
          (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))
          le_sup_left)) ∧
        actualCurveCoordinateHilbertDegree C = finiteSchemeRank (toBase
          (C ⊔ equationIdeal (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j))) ∧
        actualCurveCoordinateHilbertDegree C ≤ 3 * n ∧
        ∃ N : ℕ, ∀ m, N ≤ m →
          finrank K (grading C (m + 1)) = finrank K (grading C m) +
            actualCurveCoordinateHilbertDegree C := by
  classical
  letI : C.toIdeal.IsPrime := hprime
  have hq0 : q ≠ 0 := by
    intro hz
    apply hnot
    rw [hz]
    exact Ideal.zero_mem _
  have hqC : q ∈ C.toIdeal := by
    apply hIC
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (by simp)
  have hn : 1 ≤ n := homogeneousEquation_degree_pos_of_mem_prime q n hq hq0 C.toIdeal hprime hqC
  obtain ⟨j, hj, hnotC, hfinite, hcartier⟩ :=
    selectedProjectivePrimeComponent_exists_coordinate_finiteCartierCut
      p q hp hp0 n hq hnot C hIC hprime P
  letI := hfinite
  obtain ⟨heq, N, hN⟩ := primeComponent_linearSection_degree_and_eventualIncrement_anyField
    C (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X K j) hnotC
  have hbound := selectedProjectiveComponent_eventualIncrement_le_three_degree_anyField
    p q hp hp0 n hn hq hnot C hIC _ N hN
  refine ⟨j, hj, hnotC, hfinite, hcartier, heq, heq.trans_le hbound, N, ?_⟩
  intro m hm
  rw [heq]
  exact hN m hm

end PfaffianDescent.Coray
