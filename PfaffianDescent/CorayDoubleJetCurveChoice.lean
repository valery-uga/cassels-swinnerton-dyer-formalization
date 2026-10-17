import PfaffianDescent.CorayHomogeneousCurveChoice
import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.Algebra.Algebra.Prod

/-!
# Actual full first jets in Coray's exceptional-degree branch

SOURCE DRAFT: not compiler checked.

The infinitesimal algebra is the explicit length-three square-zero plane
`M ⊕ M²`, with arbitrary residue and two tangent vectors. For a degree-three
residue field it imposes at most nine ground-field conditions. A degree-n
equation through another degree-d point and this full jet is constructed
outside the cubic ideal whenever the actual Hilbert function exceeds d+9.
This is the polynomial choice in Coray, p290 (A)(iii), not the subsequent
genus drop or divisor descent.
-/

namespace PfaffianDescent.Coray

open MvPolynomial Module TrivSqZeroExt
universe u

/-- The full two-dimensional square-zero first jet, of residue length three. -/
abbrev SurfacePlaneJet (M : Type u) [Field M] :=
  TrivSqZeroExt M (Fin 2 → M)

/-- Homogeneous coordinates of the actual full first jet. -/
def surfacePlaneJetCoordinates {M : Type u} [Field M]
    (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M) (i : Fin 4) :
    SurfacePlaneJet M :=
  inl (z i) + inr (fun r => v r i)

/-- A first jet over a degree-e residue field has ground-field length 3e. -/
theorem surfacePlaneJet_finrank
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] :
    finrank K (SurfacePlaneJet M) = 3 * finrank K M := by
  change finrank K (M × (Fin 2 → M)) = _
  simp [Module.finrank_prod, Module.finrank_pi_fintype, Nat.mul_comm] <;> omega

/-- Full first jets at a degree-three point impose nine conditions. -/
theorem surfacePlaneJet_degree_three_finrank
    {K M : Type u} [Field K] [Field M] [Algebra K M]
    [FiniteDimensional K M] (hM : finrank K M = 3) :
    finrank K (SurfacePlaneJet M) = 9 := by
  rw [surfacePlaneJet_finrank, hM]

/-- A single reduced degree-d point plus one full surface jet over a
degree-three residue field leaves a genuine degree-n equation whenever the
section count exceeds d+9. No existence of an intersection curve, or of its
genus drop, is assumed here. -/
theorem exists_homogeneous_curve_through_point_and_full_jet
    {K L M : Type u} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (n : ℕ) (y : Fin 4 → L) (z : Fin 4 → M)
    (v : Fin 2 → Fin 4 → M)
    (hsize : finrank K L + 3 * finrank K M <
      (n + 3).choose 3 - n.choose 3) :
    ∃ q : MvPolynomial (Fin 4) K,
      q.IsHomogeneous n ∧ q.eval₂ (algebraMap K L) y = 0 ∧
      q.eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates z v) = 0 ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
  classical
  let J := SurfacePlaneJet M
  letI : FiniteDimensional K J := by
    change FiniteDimensional K (M × (Fin 2 → M))
    infer_instance
  let x : Fin 4 → L × J := fun i => (y i, surfacePlaneJetCoordinates z v i)
  have hdim : finrank K (L × J) = finrank K L + 3 * finrank K M := by
    rw [Module.finrank_prod, surfacePlaneJet_finrank]
  obtain ⟨q, hq, hzero, hnot⟩ :=
    exists_homogeneous_curve_equation p hp hne n x (by rwa [hdim])
  have hzero' : aeval (R := K) x q = 0 := hzero
  have hy : aeval (R := K) y q = 0 := by
    have h := congrArg (AlgHom.fst K L J) hzero'
    rw [MvPolynomial.comp_aeval_apply] at h
    simpa only [x, AlgHom.fst_apply, map_zero] using h
  have hz : aeval (R := K) (surfacePlaneJetCoordinates z v) q = 0 := by
    have h := congrArg (AlgHom.snd K L J) hzero'
    rw [MvPolynomial.comp_aeval_apply] at h
    simpa only [x, AlgHom.snd_apply, map_zero] using h
  exact ⟨q, hq, hy, hz, hnot⟩

/-- The exact d+9 condition count used in Coray's double-point branch. -/
theorem exists_homogeneous_curve_through_point_and_degree_three_full_jet
    {K L M : Type u} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (n : ℕ) (y : Fin 4 → L) (z : Fin 4 → M)
    (v : Fin 2 → Fin 4 → M) (hM : finrank K M = 3)
    (hsize : finrank K L + 9 < (n + 3).choose 3 - n.choose 3) :
    ∃ q : MvPolynomial (Fin 4) K,
      q.IsHomogeneous n ∧ q.eval₂ (algebraMap K L) y = 0 ∧
      q.eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates z v) = 0 ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
  apply exists_homogeneous_curve_through_point_and_full_jet p hp hne n y z v
  simpa only [hM] using hsize

/-- In the boundary-degree case of Coray (A)(iii), the point degree equals
the preceding cubic-surface section count. For n at least four the next
section space has room for all nine jet conditions. Thus no strict section
inequality is left as an input in this branch. The corresponding values for
n=2 and n=3 are the exceptional point degrees four and ten. -/
theorem exists_boundary_degree_curve_with_degree_three_full_jet
    {K L M : Type u} [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (m : ℕ) (hm : 3 ≤ m) (y : Fin 4 → L) (z : Fin 4 → M)
    (v : Fin 2 → Fin 4 → M) (hM : finrank K M = 3)
    (hL : finrank K L = (m + 3).choose 3 - m.choose 3) :
    ∃ q : MvPolynomial (Fin 4) K,
      q.IsHomogeneous (m + 1) ∧ q.eval₂ (algebraMap K L) y = 0 ∧
      q.eval₂ (algebraMap K (SurfacePlaneJet M))
        (surfacePlaneJetCoordinates z v) = 0 ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
  apply exists_homogeneous_curve_through_point_and_degree_three_full_jet
    p hp hne (m + 1) y z v hM
  have hjump := cubicSurface_grade_succ_finrank_all p hp hne m
  rw [cubicSurface_grade_finrank p hp hne (m + 1),
    cubicSurface_grade_finrank p hp hne m] at hjump
  omega

end PfaffianDescent.Coray
