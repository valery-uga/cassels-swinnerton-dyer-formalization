import Mathlib.Algebra.Group.Pi.Basic

/-! Surjective simultaneous evaluation separates the actual evaluation
points when every target fibre has a nonzero element. -/
namespace PfaffianDescent
universe u v w z

theorem dependentPointEvaluation_points_injective
    {ι : Type u} {A : Type v} {T : Type w}
    (V : A → Type z) [∀ a, Zero (V a)]
    (r : ι → A) (ev : ∀ a, T → V a)
    (honto : Function.Surjective (fun t i => ev (r i) t))
    (hne : ∀ i, ∃ v : V (r i), v ≠ 0) : Function.Injective r := by
  classical
  intro i j hij
  by_contra hneij
  obtain ⟨v, hv⟩ := hne i
  obtain ⟨t, ht⟩ := honto (Pi.single i v)
  have hi : ev (r i) t = v := by
    simpa using congrFun ht i
  have hj : ev (r j) t = 0 := by
    simpa [show j ≠ i from fun h => hneij h.symm] using congrFun ht j
  have he : HEq (ev (r i) t) (ev (r j) t) := by
    rw [hij]
  have hz : HEq (0 : V (r i)) (0 : V (r j)) := by
    rw [hij]
  rw [hi, hj] at he
  exact hv (eq_of_heq (he.trans hz.symm))

end PfaffianDescent
