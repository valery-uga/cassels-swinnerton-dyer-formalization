import Mathlib.Algebra.DualNumber
import Mathlib.Tactic.Ring

/-! Every change of dual-number generator rescales the tangent by one nonzero
scalar. This applies to the algebra of any given double point. -/

noncomputable section
namespace PfaffianDescent
open TrivSqZeroExt
universe u
variable {K : Type u} [Field K]

/-- An arbitrary algebra automorphism of the dual numbers scales epsilon;
no prior tangent-coordinate comparison is assumed. -/
theorem dualNumber_algEquiv_scales_tangent (e : DualNumber K ≃ₐ[K] DualNumber K) :
    ∃ c : K, c ≠ 0 ∧ ∀ z : DualNumber K,
      e z = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr (c * z.snd) := by
  let t := e (DualNumber.eps : DualNumber K)
  have ht2 : t * t = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have hfst : t.fst = 0 := by
    have h := congrArg TrivSqZeroExt.fst ht2
    have hmul : t.fst * t.fst = 0 := by simpa using h
    exact (mul_eq_zero.mp hmul).elim id id
  have ht0 : t ≠ 0 := by
    intro ht
    have heps : (DualNumber.eps : DualNumber K) = 0 := e.injective (by simpa using ht)
    have h := congrArg TrivSqZeroExt.snd heps
    exact one_ne_zero (by simpa [DualNumber.eps] using h)
  have hsnd : t.snd ≠ 0 := by
    intro h
    apply ht0
    apply TrivSqZeroExt.ext <;> assumption
  have ht : t = TrivSqZeroExt.inr t.snd := by
    apply TrivSqZeroExt.ext <;> simp [hfst]
  refine ⟨t.snd, hsnd, ?_⟩
  intro z
  calc
    e z = e (TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr z.snd) :=
      congrArg e z.inl_fst_add_inr_snd_eq.symm
    _ = TrivSqZeroExt.inl z.fst + z.snd • t := by
      rw [map_add, DualNumber.inr_eq_smul_eps, map_smul]
      congr 1
      exact e.commutes z.fst
    _ = TrivSqZeroExt.inl z.fst + TrivSqZeroExt.inr (t.snd * z.snd) := by
      rw [ht]
      simp [← TrivSqZeroExt.inr_smul, smul_eq_mul, mul_comm]

/-- Two independently extracted dual-number presentations of the SAME actual
algebra give the same tangent line. -/
theorem actual_dual_presentations_differ_by_tangent_scale
    {A : Type u} [CommRing A] [Algebra K A]
    (e₁ e₂ : A ≃ₐ[K] DualNumber K) :
    ∃ c : K, c ≠ 0 ∧ ∀ x : A,
      (e₂ x).fst = (e₁ x).fst ∧ (e₂ x).snd = c * (e₁ x).snd := by
  obtain ⟨c, hc, h⟩ := dualNumber_algEquiv_scales_tangent (e₁.symm.trans e₂)
  refine ⟨c, hc, ?_⟩
  intro x
  have hx := h (e₁ x)
  have hx' : e₂ x = TrivSqZeroExt.inl (e₁ x).fst +
      TrivSqZeroExt.inr (c * (e₁ x).snd) := by simpa using hx
  exact ⟨by simpa using congrArg TrivSqZeroExt.fst hx',
    by simpa using congrArg TrivSqZeroExt.snd hx'⟩

end PfaffianDescent
