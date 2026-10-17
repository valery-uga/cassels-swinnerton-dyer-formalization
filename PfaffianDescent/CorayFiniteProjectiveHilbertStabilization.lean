import PfaffianDescent.ProjectiveLengthOfHilbert
import Mathlib.Data.Nat.Find
import Mathlib.Order.Monotone.Basic
import Lean.Elab.Tactic.Omega

/-!
# Actual finite-projective Hilbert function stabilizes at actual scheme rank

Construct a nowhere-vanishing linear form on the ACTUAL finite projective
quotient. Actual irrelevant-radical geometry derives eventual surjectivity of
grade multiplication, hence decreasing finite dimensions attain their minimum.
The constant and threshold are constructed; no eventual Hilbert-function,
constant-polynomial, desired length or degree certificate is supplied.
SOURCE ONLY / UNVERIFIED: root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [Infinite K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ACTUAL homogeneous Hilbert function of a finite projective quotient
is eventually the ACTUAL scheme rank. No eventual dimension/length conclusion
is a premise. This is a genuine constant-Hilbert-polynomial construction for
zero-dimensional quotients, needed for actual component intersections. -/
theorem finiteProjectiveHomogeneousIdeal_hilbertFunction_eventually_eq_rank
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    [IsFinite (toBase I)] :
    ∃ N : ℕ, ∀ m, N ≤ m →
      finrank K (grading I m) = finiteSchemeRank (toBase I) := by
  classical
  letI : ∀ m, Module.Finite K (grading I m) := polynomialQuotientGrade_finite I
  obtain ⟨z, hz, hnz⟩ := finite_projective_exists_nowhere_vanishing_linear I
  obtain ⟨N, hN⟩ := quotient_grade_eventually_mem_span I z hz hnz
  let H : ℕ → ℕ := fun n => finrank K (grading I (N + n))
  have hstep : ∀ n, H (n + 1) ≤ H n := by
    intro n
    have hs := homogeneousGradeMul_surjective (grading I) hz (N + n)
      (hN (N + n + 1) (by omega))
    have hle := LinearMap.finrank_le_finrank_of_surjective hs
    exact (congrArg (fun d => finrank K (grading I d))
      (Nat.add_assoc N n 1)).symm.le.trans hle
  have hanti : Antitone H := antitone_nat_of_succ_le hstep
  have hex : ∃ D : ℕ, ∃ n : ℕ, H n = D := ⟨H 0, 0, rfl⟩
  let D := Nat.find hex
  obtain ⟨n₀, hn₀⟩ := Nat.find_spec hex
  have hmin : ∀ n, D ≤ H n := fun n => Nat.find_min' hex ⟨n, rfl⟩
  have hconst : ∀ m, N + n₀ ≤ m → finrank K (grading I m) = D := by
    intro m hm
    have hn : n₀ ≤ m - N := by omega
    have hupper : H (m - N) ≤ D := by
      exact (hanti hn).trans_eq hn₀
    have heq : H (m - N) = D := le_antisymm hupper (hmin (m - N))
    have hindex : N + (m - N) = m := by omega
    dsimp only [H] at heq
    rw [hindex] at heq
    exact heq
  have hlength : finiteSchemeRank (toBase I) = D :=
    projective_length_of_eventual_hilbert I (N + n₀) D hconst
  refine ⟨N + n₀, ?_⟩
  intro m hm
  rw [hlength]
  exact hconst m hm

end PfaffianDescent.Coray
