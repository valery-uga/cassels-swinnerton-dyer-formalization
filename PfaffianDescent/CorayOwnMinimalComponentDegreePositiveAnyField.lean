import PfaffianDescent.CorayOwnMinimalComponentNonfiniteAnyField
import PfaffianDescent.CorayOwnCoordinateHilbertDegreeAnyField

/-! SOURCE ONLY / UNVERIFIED; actual degree construction130 is pending.
Strict positivity belongs to SAME selected minimal component, not an arbitrary
prime containing the pair. Original K and original OWN degree are retained. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem projective_toBase_finite_of_zero_eventualIncrement
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (N : ℕ)
    (hN : ∀ m, N ≤ m → finrank K (grading C (m + 1)) = finrank K (grading C m)) :
    IsFinite (toBase C) := by
  have hconstant : ∀ t : ℕ, finrank K (grading C (N + t)) = finrank K (grading C N) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hstep := hN (N + t) (by omega)
      have hindex : finrank K (grading C (N + Nat.succ t)) =
          finrank K (grading C (N + t + 1)) :=
        (congrArg (fun d => finrank K (grading C d)) (Nat.add_assoc N t 1)).symm
      exact hindex.trans (hstep.trans ih)
  exact PfaffianDescent.projective_finite_of_hilbert_bound C N (finrank K (grading C N)) (by
    intro m hm
    have hindex : N + (m - N) = m := by omega
    have hdim := congrArg (fun d => finrank K (grading C d)) hindex
    exact (hdim.symm.trans (hconstant (m - N))).le)

/-- The actual original selected minimal component has positive OWN degree
at most3n, with genuinely constructed eventual increments over ANY field.
No dim/nonfinite/degree/finite-cut/genus premise is supplied. -/
theorem selectedProjectiveMinimalComponent_hilbertDegree_pos_bound_and_eventualIncrement_anyField
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    0 < actualCurveCoordinateHilbertDegree C ∧
      actualCurveCoordinateHilbertDegree C ≤ 3 * n ∧
      ∃ N : ℕ, ∀ m, N ≤ m →
        finrank K (grading C (m + 1)) = finrank K (grading C m) +
          actualCurveCoordinateHilbertDegree C := by
  classical
  have hrel := selectedProjectiveMinimalComponent_homogeneous_relevant p q hp hp0 n hq hnot C hCmin
  let P := homogeneousPrimeQuotientProjectivePoint C hCmin.isPrime hrel
  obtain ⟨_j, _hj, _hnotC, _hfinite, _hcartier, _heq, hbound, N, hN⟩ :=
    selectedProjectivePrimeComponent_exists_coordinateCartierCut_degree_bound_anyField
      p q hp hp0 n hq hnot C hCmin.le hCmin.isPrime P
  have hpos : 0 < actualCurveCoordinateHilbertDegree C := by
    by_contra h
    have hz : actualCurveCoordinateHilbertDegree C = 0 := by omega
    have hincrement : ∀ m, N ≤ m → finrank K (grading C (m + 1)) = finrank K (grading C m) := by
      intro m hm
      simpa only [hz, Nat.add_zero] using hN m hm
    exact selectedProjectiveMinimalComponent_toBase_not_isFinite_anyField
      p q hp hp0 n hq hnot C hCmin
      (projective_toBase_finite_of_zero_eventualIncrement C N hincrement)
  exact ⟨hpos, hbound, N, hN⟩

end PfaffianDescent.Coray
