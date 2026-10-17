import PfaffianDescent.CorayComponentHilbertFunctionBound
import PfaffianDescent.CorayActualComponentHilbertDegree
import Mathlib.Tactic.Linarith

/-! SOURCE ONLY / UNVERIFIED. Independent original-field algebra and
asymptotic cuts. No Infinite/Perfect assumption; no degree/genus bound premise. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonzero homogeneous equation in a proper prime has positive degree. -/
theorem homogeneousEquation_degree_pos_of_mem_prime
    {K : Type u} [Field K] (q : MvPolynomial (Fin 4) K) (n : ℕ)
    (hq : q.IsHomogeneous n) (hq0 : q ≠ 0)
    (J : Ideal (MvPolynomial (Fin 4) K)) (hJ : J.IsPrime) (hqJ : q ∈ J) :
    1 ≤ n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  have hdeg : q.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin 4)).mpr (hn0 ▸ hq)
  have heq : q = MvPolynomial.C (q.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hc : q.coeff 0 ≠ 0 := by
    intro hz
    apply hq0
    rw [heq, hz, map_zero]
  have hunit : IsUnit q := by
    rw [heq]
    exact (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
  exact hJ.ne_top (J.eq_top_of_isUnit_mem hqJ hunit)

/-- Ordinary uniqueness for the actual intrinsic increment definition. -/
theorem actualCoordinateDegree_eq_eventualIncrement_anyField
    {K : Type u} [Field K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (μ N : ℕ)
    (hN : ∀ m, N ≤ m →
      finrank K (grading C (m + 1)) = finrank K (grading C m) + μ) :
    actualCurveCoordinateHilbertDegree C = μ := by
  classical
  have hex : ∃ ν : ℕ, ∃ M : ℕ, ∀ m, M ≤ m →
      finrank K (grading C (m + 1)) = finrank K (grading C m) + ν := ⟨μ, N, hN⟩
  change (if h : ∃ ν : ℕ, ∃ M : ℕ, ∀ m, M ≤ m →
    finrank K (grading C (m + 1)) = finrank K (grading C m) + ν
    then Nat.find h else 0) = μ
  rw [dif_pos hex]
  obtain ⟨M, hM⟩ := Nat.find_spec hex
  have hfirst := hN (max N M) (le_max_left _ _)
  have hsecond := hM (max N M) (le_max_right _ _)
  omega

/-- The actual whole-pair every-grade Koszul bound bounds any derived
constant increment of its actual quotient, over the original field. -/
theorem selectedProjectiveComponent_eventualIncrement_le_three_degree_anyField
    {K : Type u} [Field K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIC : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ C.toIdeal)
    (μ N : ℕ)
    (hN : ∀ m, N ≤ m →
      finrank K (grading C (m + 1)) = finrank K (grading C m) + μ) :
    μ ≤ 3 * n := by
  let B := max N (n + 3)
  have hAffine : ∀ t : ℕ, finrank K (grading C (B + t)) =
      finrank K (grading C B) + t * μ := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have hstep := hN (B + t) (by dsimp only [B]; omega)
      rw [ih] at hstep
      have hindex : finrank K (grading C (B + Nat.succ t)) =
          finrank K (grading C (B + t + 1)) :=
        (congrArg (fun d => finrank K (grading C d)) (Nat.add_assoc B t 1)).symm
      simpa only [Nat.succ_mul, Nat.add_assoc] using hindex.trans hstep
  by_contra hle
  have hgap : 3 * n + 1 ≤ μ := by omega
  let t := 3 * n * B + 1
  let d := B + t - (n + 3)
  have hidx : d + n + 3 = B + t := by dsimp only [d, B]; omega
  have hdim : finrank K (grading C (d + n + 3)) = finrank K (grading C (B + t)) :=
    congrArg (fun m => finrank K (grading C m)) hidx
  have hwhole := selectedProjectiveComponent_hilbertFunction_linearBound
    p q hp hp0 n hn hq hnot C hIC d
  rw [hdim, hidx, hAffine t] at hwhole
  have hproduct := Nat.mul_le_mul_left t hgap
  dsimp only [t] at hwhole hproduct
  nlinarith only [hwhole, hproduct, Nat.zero_le (finrank K (grading C B)),
    Nat.zero_le (3 * n * (n - 1))]

end PfaffianDescent.Coray
