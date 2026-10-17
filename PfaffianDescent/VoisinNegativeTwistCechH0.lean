import PfaffianDescent.VoisinTwistCechExact
import PfaffianDescent.P3PositiveTwistGlobalSections

/-!
# Degree-zero Čech vanishing for negative twists on projective three-space

A degree-zero Čech cocycle has the same Laurent representative on every
coordinate chart. For `O(-m)` with `m > 0`, its monomials would have negative
total degree while having no negative exponent, so the cocycle is zero.
-/

noncomputable section

namespace PfaffianDescent.ProjectiveNegativeTwist

open CategoryTheory AlgebraicGeometry
open LaurentLocalization LaurentCechCore TwistCechTerms

universe u

variable (K : Type u) [Field K]

/-- A Laurent polynomial of negative total degree whose monomials all have
nonnegative exponents is zero. -/
theorem laurent_eq_zero_of_negative_degree_and_nonnegative_support
    (m : ℕ) (hm : 0 < m)
    (g : LaurentLocalization.LaurentPolynomial K)
    (hg : ∀ a ∈ g.coeff.support,
      LaurentLocalization.totalDegree a = -(m : ℤ) ∧ negativeSupport a = ∅) :
    g = 0 := by
  ext a
  by_contra ha
  have hmem : a ∈ g.coeff.support := Finsupp.mem_support_iff.mpr ha
  obtain ⟨hdegree, hsupport⟩ := hg a hmem
  have hnonneg (i : Fin 4) : 0 ≤ a i := by
    by_contra hi
    have hineg : i ∈ negativeSupport a := by
      change a i < 0
      omega
    rw [hsupport] at hineg
    simp at hineg
  have htotal : 0 ≤ LaurentLocalization.totalDegree a := by
    unfold LaurentLocalization.totalDegree
    exact Finset.sum_nonneg fun i _ => hnonneg i
  omega

/-- For a strictly negative twist, the first differential of the raw
standard-cover Čech complex is injective. -/
theorem p3NegativeTwistCech_d_zero_injective_of_pos
    (m : ℕ) (hm : 0 < m) :
    Function.Injective ((p3NegativeTwistCechComplex (K := K) m).d 0 1) := by
  let C := p3NegativeTwistCechComplex (K := K) m
  have hzero (z : C.X 0) (hz : C.d 0 1 z = 0) : z = 0 := by
    let g : Fin 4 → LaurentLocalization.LaurentPolynomial K :=
      fun i => p3NegativeTwistCechTermToLaurent K m 0 z ![i]
    have hsame (i j : Fin 4) : g i = g j := by
      have h := congrFun (p3NegativeTwistCechTermToLaurent_d_zero K m z)
        ![i, j]
      rw [hz, map_zero] at h
      change (0 : LaurentLocalization.LaurentPolynomial K) = g j - g i at h
      exact (sub_eq_zero.mp h.symm).symm
    have hgone : g 0 = 0 := by
      apply laurent_eq_zero_of_negative_degree_and_nonnegative_support
        K m hm
      intro a ha
      have hzeroSupport :=
        p3NegativeTwistCechTermToLaurent_support_properties K m 0 z ![0] a ha
      have haone : a ∈ (g 1).coeff.support := by
        rw [← hsame 0 1]
        exact ha
      have honeSupport :=
        p3NegativeTwistCechTermToLaurent_support_properties K m 0 z ![1]
          a haone
      refine ⟨hzeroSupport.1, ?_⟩
      apply negativeSupport_eq_empty_of_subset_singletons a
      · simpa using hzeroSupport.2
      · simpa using honeSupport.2
    have hforall (i : Fin 4) : g i = 0 :=
      (hsame i 0).trans hgone
    apply p3NegativeTwistCechTermToLaurent_injective K m 0
    funext f
    have hf : f = ![f 0] := by
      funext i
      fin_cases i
      rfl
    rw [hf]
    simpa [g] using hforall (f 0)
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

end PfaffianDescent.ProjectiveNegativeTwist
