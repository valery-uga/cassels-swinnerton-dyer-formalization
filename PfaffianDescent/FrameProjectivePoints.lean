import PfaffianDescent.FrameProjectiveIdeal
import Mathlib.Data.Set.Card

namespace PfaffianDescent
open MvPolynomial
section
variable {K : Type*} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma frameProjectivePoint_X_mem (p : Option (Fin 4)) (i : Fin 4) :
    (X i : MvPolynomial (Fin 4) K) ∈ (frameProjectivePoint (K := K) p).asHomogeneousIdeal ↔
      ∃ j : Fin 4, p = some j ∧ i ≠ j := by
  rw [frameProjectivePoint_mem_iff, aeval_X]
  cases p with
  | none => simp only [frameLineVariable, Polynomial.X_ne_zero, reduceCtorEq, false_and,
      exists_const]
  | some j =>
      by_cases h : i = j <;>
        simp [frameLineVariable, h, Polynomial.X_ne_zero]

/-- The four coordinate points and the diagonal are five distinct projective points. -/
theorem frameProjectivePoint_injective : Function.Injective (frameProjectivePoint (K := K)) := by
  intro p q h
  have hm (i : Fin 4) : (∃ j : Fin 4, p = some j ∧ i ≠ j) ↔
      (∃ j : Fin 4, q = some j ∧ i ≠ j) := by
    rw [← frameProjectivePoint_X_mem (K := K), ← frameProjectivePoint_X_mem (K := K), h]
  cases p with
  | none =>
      cases q with
      | none => rfl
      | some j =>
          obtain ⟨i, hi⟩ := exists_ne j
          obtain ⟨k, hk, _⟩ := (hm i).mpr ⟨j, rfl, hi⟩
          cases hk
  | some i =>
      cases q with
      | none =>
          obtain ⟨j, hj⟩ := exists_ne i
          obtain ⟨k, hk, _⟩ := (hm j).mp ⟨i, rfl, hj⟩
          cases hk
      | some j =>
          by_contra hne
          have hij : i ≠ j := fun e => hne (congrArg some e)
          obtain ⟨k, hk, hik⟩ := (hm i).mpr ⟨j, rfl, hij⟩
          exact hik (Option.some.inj hk)

/-- The projective vanishing-ideal calculation concerns exactly five points. -/
theorem frameProjectivePoint_card : (Set.range (frameProjectivePoint (K := K))).ncard = 5 := by
  rw [Set.ncard_range_of_injective frameProjectivePoint_injective]
  simp

end
end PfaffianDescent
