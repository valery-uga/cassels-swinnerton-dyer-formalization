import PfaffianDescent.CorayDoubleJetCurveChoice
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Derivatives of the equations actually selected for Coray's descent

SOURCE DRAFT: not compiler checked.

Vanishing on the explicit square-zero plane is translated into vanishing
of the equation and both actual directional derivatives. In particular,
the first-jet premise in the previous module is not an uninterpreted
geometric certificate. The later surface double-point and genus-drop
comparisons remain open.
-/

namespace PfaffianDescent.Coray
open MvPolynomial Module TrivSqZeroExt
universe u

section
variable {K M : Type u} [Field K] [Field M] [Algebra K M]

noncomputable def homogeneousDirectionalJet (z w : Fin 4 → M) :
    MvPolynomial (Fin 4) K →ₐ[K] DualNumber M :=
  aeval (fun i => inl (z i) + inr (w i))

theorem homogeneousDirectionalJet_fst (z w : Fin 4 → M)
    (q : MvPolynomial (Fin 4) K) :
    (homogeneousDirectionalJet z w q).fst = aeval z q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [homogeneousDirectionalJet, TrivSqZeroExt.algebraMap_eq_inl']
  | add q r hq hr => simp only [map_add, fst_add, hq, hr]
  | mul_X q j hq =>
    rw [map_mul, fst_mul, hq]
    simp [homogeneousDirectionalJet]

theorem homogeneousDirectionalJet_snd (z w : Fin 4 → M)
    (q : MvPolynomial (Fin 4) K) :
    (homogeneousDirectionalJet z w q).snd =
      ∑ i, aeval z (pderiv i q) * w i := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [homogeneousDirectionalJet, TrivSqZeroExt.algebraMap_eq_inl']
  | add q r hq hr =>
    simp only [map_add, snd_add, hq, hr, add_mul, Finset.sum_add_distrib]
  | mul_X q j hq =>
    rw [map_mul, DualNumber.snd_mul, homogeneousDirectionalJet_fst, hq]
    have hx0 : (homogeneousDirectionalJet z w (X (R := K) j)).fst = z j := by
      simp [homogeneousDirectionalJet]
    have hx1 : (homogeneousDirectionalJet z w (X (R := K) j)).snd = w j := by
      simp [homogeneousDirectionalJet]
    rw [hx0, hx1]
    simp only [pderiv_mul, map_add, map_mul, pderiv_X, Pi.single_apply]
    fin_cases j <;> simp [Fin.sum_univ_four] <;> ring

/-- Each of the two directional dual points is the explicit projection of
the full plane jet by the corresponding coordinate linear map. -/
theorem surfacePlaneJet_projects_to_directionalJet
    (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M) (r : Fin 2)
    (q : MvPolynomial (Fin 4) K) :
    (TrivSqZeroExt.map (LinearMap.proj r : (Fin 2 → M) →ₗ[M] M))
        (aeval (R := K) (surfacePlaneJetCoordinates z v) q) =
      homogeneousDirectionalJet z (v r) q := by
  let φ : SurfacePlaneJet M →ₐ[K] DualNumber M :=
    (TrivSqZeroExt.map (LinearMap.proj r : (Fin 2 → M) →ₗ[M] M)).restrictScalars K
  have h := MvPolynomial.comp_aeval_apply
    (f := surfacePlaneJetCoordinates z v) φ q
  have hcoords : (fun i => φ (surfacePlaneJetCoordinates z v i)) =
      (fun i => (inl (z i) + inr (v r i) : DualNumber M)) := by
    funext i
    simp [φ, surfacePlaneJetCoordinates, LinearMap.proj_apply]
  rw [hcoords] at h
  exact h

/-- Full-jet vanishing forces the residue value and both actual directional
derivatives to vanish. -/
theorem value_and_directional_derivatives_zero_of_full_jet_zero
    (z : Fin 4 → M) (v : Fin 2 → Fin 4 → M)
    (q : MvPolynomial (Fin 4) K)
    (hjet : q.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates z v) = 0) :
    q.eval₂ (algebraMap K M) z = 0 ∧
      ∀ r : Fin 2, ∑ i, (pderiv i q).eval₂ (algebraMap K M) z * v r i = 0 := by
  have hdir (r : Fin 2) : homogeneousDirectionalJet z (v r) q = 0 := by
    rw [← surfacePlaneJet_projects_to_directionalJet z v r q]
    change (TrivSqZeroExt.map (LinearMap.proj r : (Fin 2 → M) →ₗ[M] M))
      (q.eval₂ (algebraMap K (SurfacePlaneJet M)) (surfacePlaneJetCoordinates z v)) = 0
    rw [hjet, map_zero]
  constructor
  · have h := congrArg TrivSqZeroExt.fst (hdir 0)
    simpa only [homogeneousDirectionalJet_fst, fst_zero, MvPolynomial.aeval_def] using h
  · intro r
    have h := congrArg TrivSqZeroExt.snd (hdir r)
    simpa only [homogeneousDirectionalJet_snd, snd_zero, MvPolynomial.aeval_def] using h

/-- Coray's d+9 count yields an actual degree-n equation through the degree-d
coordinates with both derivatives zero at the degree-three coordinates;
the defining cubic does not divide it. -/
theorem exists_homogeneous_curve_with_two_derivatives_zero
    {L : Type u} [Field L] [Algebra K L]
    [FiniteDimensional K L] [FiniteDimensional K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0)
    (n : ℕ) (y : Fin 4 → L) (z : Fin 4 → M)
    (v : Fin 2 → Fin 4 → M) (hM : finrank K M = 3)
    (hsize : finrank K L + 9 < (n + 3).choose 3 - n.choose 3) :
    ∃ q : MvPolynomial (Fin 4) K,
      q.IsHomogeneous n ∧ q.eval₂ (algebraMap K L) y = 0 ∧
      q.eval₂ (algebraMap K M) z = 0 ∧
      (∀ r : Fin 2,
        ∑ i, (pderiv i q).eval₂ (algebraMap K M) z * v r i = 0) ∧
      q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)) := by
  obtain ⟨q, hq, hy, hjet, hnot⟩ :=
    exists_homogeneous_curve_through_point_and_degree_three_full_jet
      p hp hne n y z v hM hsize
  obtain ⟨hz, hd⟩ := value_and_directional_derivatives_zero_of_full_jet_zero z v q hjet
  exact ⟨q, hq, hy, hz, hd, hnot⟩

end
end PfaffianDescent.Coray
