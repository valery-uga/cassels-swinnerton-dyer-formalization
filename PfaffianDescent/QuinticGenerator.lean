import PfaffianDescent.QuinticPowerBasis

namespace PfaffianDescent
open Module
open scoped IntermediateField

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- In a degree-five extension, every element outside the ground field is primitive. -/
theorem quintic_generator_adjoin (hdim : finrank K L = 5) (α : L)
    (hα : α ∉ (⊥ : IntermediateField K L)) : K⟮α⟯ = ⊤ := by
  let : IsSimpleOrder (IntermediateField K L) :=
    IntermediateField.isSimpleOrder_of_finrank_prime K L (by rw [hdim]; decide)
  rcases eq_bot_or_eq_top K⟮α⟯ with h | h
  · exact False.elim (hα (h ▸ IntermediateField.mem_adjoin_simple_self K α))
  · exact h

/-- The power basis at a specified nonground-field element of a quintic extension. -/
theorem quintic_generator_basis (hdim : finrank K L = 5) (α : L)
    (hα : α ∉ (⊥ : IntermediateField K L)) :
    ∃ b : Basis (Fin 5) K L, ∀ i, b i = α^(i : ℕ) := by
  have htop := quintic_generator_adjoin hdim α hα
  let p := IntermediateField.adjoin.powerBasis (Algebra.IsIntegral.isIntegral (R := K) α)
  let e := (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  let q := p.map e
  have hgen : q.gen = α := rfl
  have hdimq : q.dim = 5 := q.finrank.symm.trans hdim
  refine ⟨q.basis.reindex (finCongr hdimq), ?_⟩
  intro i
  rw [Basis.reindex_apply, q.basis_eq_pow, hgen]
  rfl

end
end PfaffianDescent
