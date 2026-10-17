import PfaffianDescent.Specialization

namespace PfaffianDescent
open Polynomial

section
variable {K : Type*} [Field K]

/-- Remove a common power of `X-t` while retaining any relation that cancels
this common factor. This also applies to relations with values in an extension ring. -/
theorem normalize_polynomial_relation {ι : Type*} (t : K)
    (P : (ι → K[X]) → Prop)
    (hstep : ∀ q, P ((X - C t) • q) → P q)
    (p : ι → K[X]) (hp : p ≠ 0) (hP : P p) :
    ∃ q : ι → K[X], P q ∧ ∃ i, (q i).eval t ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (funext h)
  suffices ∀ n, ∀ p : ι → K[X], p i ≠ 0 → (p i).natDegree = n → P p →
      ∃ q : ι → K[X], P q ∧ ∃ j, (q j).eval t ≠ 0 by
    exact this _ p hi rfl hP
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hpi hn hPp
    by_cases hc : ∃ j, (p j).eval t ≠ 0
    · exact ⟨p, hPp, hc⟩
    push Not at hc
    let q : ι → K[X] := fun j => p j /ₘ (X - C t)
    have hq : (X - C t) • q = p := by
      funext j
      exact mul_divByMonic_eq_iff_isRoot.mpr (hc j)
    have hqi : q i ≠ 0 := by
      intro hz
      apply hpi
      have hh := congrFun hq i
      simpa only [Pi.smul_apply, smul_eq_mul, hz, mul_zero] using hh.symm
    have hdegree : (q i).natDegree < n := by
      have hh := congrArg Polynomial.natDegree (congrFun hq i)
      change ((X - C t) * q i).natDegree = (p i).natDegree at hh
      rw [natDegree_mul (X_sub_C_ne_zero t) hqi, natDegree_X_sub_C, hn] at hh
      omega
    exact ih _ hdegree q hqi rfl (hstep q (hq.symm ▸ hPp))

end
end PfaffianDescent
