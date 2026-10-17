import PfaffianDescent.CoraySelectedPrimeCurveHilbertLinearity
import PfaffianDescent.CorayComponentHilbertCoefficientInvariance
import Mathlib.Data.Nat.Find

/-!
# Intrinsic actual coordinate curve degree and actual hyperplane length

The actual coordinate curve degree is the unique eventual Hilbert increment,
when one exists (zero otherwise). Genuine prime finite-cut geometry derives
that increment and identifies it with the SAME native section scheme rank.
The original p/q caller derives existence and its degree bound internally.
Literal coefficient extension preserves this intrinsic degree through actual
every-grade tensor invariance. No degree/linearity/finite-cut certificate is
supplied to the original selected-curve caller.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

private def intrinsicEventualHilbertIncrement (h : ℕ → ℕ) : ℕ := by
  classical
  exact if hex : ∃ μ : ℕ, ∃ N : ℕ, ∀ m, N ≤ m → h (m + 1) = h m + μ
    then Nat.find hex else 0

/-- Intrinsic degree of the ACTUAL coordinate Hilbert function of a curve.
Zero is the explicit fallback if no eventual constant increment exists. The
original prime-curve construction below proves existence and removes that
fallback; this definition is not an existence or genus assumption. -/
def actualCurveCoordinateHilbertDegree
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) : ℕ :=
  intrinsicEventualHilbertIncrement (fun m => finrank K (grading I m))

private theorem actualCurveCoordinateHilbertDegree_eq_of_increment
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (μ N : ℕ)
    (hN : ∀ m, N ≤ m →
      finrank K (grading I (m + 1)) = finrank K (grading I m) + μ) :
    actualCurveCoordinateHilbertDegree I = μ := by
  classical
  let h : ℕ → ℕ := fun m => finrank K (grading I m)
  have hex : ∃ ν : ℕ, ∃ M : ℕ, ∀ m, M ≤ m → h (m + 1) = h m + ν :=
    ⟨μ, N, hN⟩
  change intrinsicEventualHilbertIncrement h = μ
  rw [intrinsicEventualHilbertIncrement, dif_pos hex]
  obtain ⟨M, hM⟩ := Nat.find_spec hex
  have hfirst := hN (max N M) (le_max_left _ _)
  have hsecond := hM (max N M) (le_max_right _ _)
  change h (max N M + 1) = h (max N M) + μ at hfirst
  omega

/-- The actual prime curve's intrinsic coordinate degree equals the SAME
literal finite hyperplane section's scheme rank, and actual increments
stabilize at that rank. The equality is independent of chosen thresholds. -/
theorem primeComponent_linearSection_degree_and_eventualIncrement
    {K : Type u} [Field K] [Infinite K]
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) [C.toIdeal.IsPrime]
    (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1) (hnot : H ∉ C.toIdeal)
    [IsFinite (toBase (C ⊔ equationIdeal H hH))] :
    actualCurveCoordinateHilbertDegree C = finiteSchemeRank (toBase (C ⊔ equationIdeal H hH)) ∧
      ∃ N : ℕ, ∀ m, N ≤ m →
        finrank K (grading C (m + 1)) = finrank K (grading C m) +
          finiteSchemeRank (toBase (C ⊔ equationIdeal H hH)) := by
  obtain ⟨N, hN⟩ := finiteProjectiveHomogeneousIdeal_hilbertFunction_eventually_eq_rank
    (C ⊔ equationIdeal H hH)
  have hincrement : ∀ m, N ≤ m →
      finrank K (grading C (m + 1)) = finrank K (grading C m) +
        finiteSchemeRank (toBase (C ⊔ equationIdeal H hH)) := by
    intro m hm
    have hstep := componentLinearGrade_hilbertFunction_recurrence C H hH hnot m
    rw [hN (m + 1) (by omega)] at hstep
    exact hstep
  exact ⟨actualCurveCoordinateHilbertDegree_eq_of_increment C _ N hincrement,
    N, hincrement⟩

/-- Original smooth cubic/q minimal-component degree existence and bound are
DERIVED. In particular the caller supplies neither a Hilbert polynomial nor
a finite section, degree, genus, or eventual increment certificate. -/
theorem selectedProjectiveMinimalComponent_degree_and_eventualIncrement_bound
    {K : Type u} [Field K] [Infinite K]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    actualCurveCoordinateHilbertDegree C ≤ 3 * n ∧ ∃ N : ℕ, ∀ m, N ≤ m →
      finrank K (grading C (m + 1)) = finrank K (grading C m) +
        actualCurveCoordinateHilbertDegree C := by
  letI : C.toIdeal.IsPrime := hCmin.isPrime
  obtain ⟨H, hH, hnotC, hfinite, _N, _hN, hbound⟩ :=
    selectedProjectiveMinimalComponent_exists_affineHilbertFunction p q hp hp0 n hq hnot C hCmin
  letI := hfinite
  obtain ⟨heq, N, hN⟩ := primeComponent_linearSection_degree_and_eventualIncrement C H hH hnotC
  constructor
  · rw [heq]
    exact hbound
  · refine ⟨N, ?_⟩
    intro m hm
    rw [heq]
    exact hN m hm

/-- Literal whole-ideal coefficient extension preserves the intrinsic actual
curve coordinate degree. Its input is actual coefficient geometry, not an
assumed degree or Hilbert-function comparison. -/
theorem actualCurveCoordinateHilbertDegree_eq_coefficientExtension
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal) :
    actualCurveCoordinateHilbertDegree J = actualCurveCoordinateHilbertDegree I :=
  congrArg intrinsicEventualHilbertIncrement (funext fun d =>
    actualComponentGrade_finrank_eq_coefficientExtension I J hIJ d)

end PfaffianDescent.Coray
