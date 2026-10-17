import PfaffianDescent.CorayRelevantPrimeComponentHyperplaneDegree
import PfaffianDescent.CorayDistinctProjectiveCurveComponentIntersectionFinite
import PfaffianDescent.CorayHomogeneousHilbertFunctionAdditivity
import Mathlib.Tactic.Linarith

/-!
# Two actual component degrees add and their sum is bounded by original3n

Actual relevant distinct minimal components C,D of I containing originalp/q
have finite OWN scheme-theoretic intersection from actual curve dimensions.
Their OWN degree increments are constructed by actual point/hyperplane geometry.
Every-grade union/intersection additivity and genuine finite stabilization
construct the union increment and derive degree additivity. Originalp/q Hilbert
bounds then give degreeC+degreeD≤3n. No component slope, finiteintersection,
degreeadditivity, arithmeticgenus or rµ certificate is supplied.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Genuine two-component degree additivity and original completeintersection
bound. I may be a coefficient extension of the already selected originalprime;
C,D need not be assumed minimal over the WHOLE originalp/q ideal. -/
theorem selectedProjectiveTwoActualComponents_degree_additivity_bound
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I C D : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hPQI : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ I.toIdeal)
    (hC : C.toIdeal ∈ I.toIdeal.minimalPrimes)
    (hCrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ C)
    (hD : D.toIdeal ∈ I.toIdeal.minimalPrimes)
    (hDrel : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) K) ≤ D)
    (hne : C ≠ D) :
    actualCurveCoordinateHilbertDegree (C ⊓ D) =
        actualCurveCoordinateHilbertDegree C + actualCurveCoordinateHilbertDegree D ∧
      actualCurveCoordinateHilbertDegree C + actualCurveCoordinateHilbertDegree D ≤ 3 * n ∧
      ∃ N : ℕ, ∀ m, N ≤ m →
        finrank K (grading (C ⊓ D) (m + 1)) = finrank K (grading (C ⊓ D) m) +
          (actualCurveCoordinateHilbertDegree C + actualCurveCoordinateHilbertDegree D) := by
  classical
  letI : C.toIdeal.IsPrime := hC.isPrime
  letI : D.toIdeal.IsPrime := hD.isPrime
  have hPQC := hPQI.trans hC.le
  have hPQD := hPQI.trans hD.le
  have hfinite : IsFinite (toBase (C ⊔ D)) :=
    homogeneousDistinctCurveComponents_sup_isFinite I C D hC hCrel hD hDrel hne
      (selectedProjectiveComponent_original_stalk_ringKrullDim_le_one p q hp hp0 n hq hnot C hPQC)
  letI := hfinite
  obtain ⟨_HC, _hHC, _hnotHC, _hfiniteC, _hdegC, _hboundC, NC, hNC⟩ :=
    selectedProjectiveRelevantPrime_exists_hyperplane_degree_bound p q hp hp0 n hq hnot C hCrel hPQC
  obtain ⟨_HD, _hHD, _hnotHD, _hfiniteD, _hdegD, _hboundD, ND, hND⟩ :=
    selectedProjectiveRelevantPrime_exists_hyperplane_degree_bound p q hp hp0 n hq hnot D hDrel hPQD
  obtain ⟨NS, hNS⟩ := finiteProjectiveHomogeneousIdeal_hilbertFunction_eventually_eq_rank (C ⊔ D)
  have hNCdegree : ∀ m, NC ≤ m →
      finrank K (grading C (m + 1)) = finrank K (grading C m) +
        actualCurveCoordinateHilbertDegree C := by
    intro m hm
    simpa only [← _hdegC] using hNC m hm
  have hNDdegree : ∀ m, ND ≤ m →
      finrank K (grading D (m + 1)) = finrank K (grading D m) +
        actualCurveCoordinateHilbertDegree D := by
    intro m hm
    simpa only [← _hdegD] using hND m hm
  let U := C ⊓ D
  let μ := actualCurveCoordinateHilbertDegree C + actualCurveCoordinateHilbertDegree D
  let N := max NC (max ND NS)
  have hincrement : ∀ m, N ≤ m →
      finrank K (grading U (m + 1)) = finrank K (grading U m) + μ := by
    intro m hm
    have hNCm : NC ≤ m := (le_max_left NC (max ND NS)).trans hm
    have hNDm : ND ≤ m := (le_max_left ND NS).trans ((le_max_right NC (max ND NS)).trans hm)
    have hNSm : NS ≤ m := (le_max_right ND NS).trans ((le_max_right NC (max ND NS)).trans hm)
    have hsum0 := homogeneousCoordinateGrade_union_intersection_finrank_additivity C D m
    have hsum1 := homogeneousCoordinateGrade_union_intersection_finrank_additivity C D (m + 1)
    rw [hNS m hNSm] at hsum0
    rw [hNS (m + 1) (by omega), hNCdegree m hNCm, hNDdegree m hNDm] at hsum1
    change finrank K (grading (C ⊓ D) (m + 1)) = finrank K (grading (C ⊓ D) m) +
      (actualCurveCoordinateHilbertDegree C + actualCurveCoordinateHilbertDegree D)
    omega
  have hdegree : actualCurveCoordinateHilbertDegree U = μ := by
    have hex : ∃ ν : ℕ, ∃ M : ℕ, ∀ m, M ≤ m →
        finrank K (grading U (m + 1)) = finrank K (grading U m) + ν := ⟨μ, N, hincrement⟩
    change (if h : ∃ ν : ℕ, ∃ M : ℕ, ∀ m, M ≤ m →
      finrank K (grading U (m + 1)) = finrank K (grading U m) + ν
      then Nat.find h else 0) = μ
    rw [dif_pos hex]
    obtain ⟨M, hM⟩ := Nat.find_spec hex
    have hfirst := hincrement (max N M) (le_max_left _ _)
    have hsecond := hM (max N M) (le_max_right _ _)
    omega
  let B := max N (n + 3)
  have hB : N ≤ B := le_max_left _ _
  have hAffine : ∀ t : ℕ, finrank K (grading U (B + t)) =
      finrank K (grading U B) + t * μ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hstep := hincrement (B + t) (by omega)
      rw [ih] at hstep
      have hindex : finrank K (grading U (B + Nat.succ t)) =
          finrank K (grading U (B + t + 1)) :=
        (congrArg (fun d => finrank K (grading U d)) (Nat.add_assoc B t 1)).symm
      simpa only [Nat.succ_mul, Nat.add_assoc] using hindex.trans hstep
  have hPQU : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ U.toIdeal := le_inf hPQC hPQD
  have hbound : μ ≤ 3 * n := by
    by_contra hle
    have hgap : 3 * n + 1 ≤ μ := by omega
    let t := 3 * n * B + 1
    let d := B + t - (n + 3)
    have hidx : d + n + 3 = B + t := by dsimp only [d, B]; omega
    have hdim : finrank K (grading U (d + n + 3)) = finrank K (grading U (B + t)) :=
      congrArg (fun m => finrank K (grading U m)) hidx
    have hwhole := selectedProjectiveComponent_hilbertFunction_linearBound
      p q hp hp0 n hn hq hnot U hPQU d
    rw [hdim, hidx, hAffine t] at hwhole
    have hproduct := Nat.mul_le_mul_left t hgap
    dsimp only [t] at hwhole hproduct
    nlinarith only [hwhole, hproduct, Nat.zero_le (finrank K (grading U B)),
      Nat.zero_le (3 * n * (n - 1))]
  exact ⟨hdegree, hbound, N, hincrement⟩

end PfaffianDescent.Coray
