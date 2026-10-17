import Mathlib.Algebra.Module.Equiv.Basic

/-! SOURCE ONLY / UNVERIFIED. Quotient lines are taken modulo an actual
isomorphism of their one-dimensional target, not equality of functionals. -/
noncomputable section
namespace PfaffianDescent
universe u
variable {L M : Type u} [Field L] [AddCommGroup M] [Module L M]

def OneDimensionalQuotientTargetIso (q₁ q₂ : M →ₗ[L] L) : Prop :=
  ∃ e : L ≃ₗ[L] L, q₂ = e.toLinearMap.comp q₁

theorem oneDimensionalQuotientTargetIso_iff_smul (q₁ q₂ : M →ₗ[L] L) :
    OneDimensionalQuotientTargetIso q₁ q₂ ↔
      ∃ c : L, c ≠ 0 ∧ q₂ = c • q₁ := by
  constructor
  · rintro ⟨e, he⟩
    have hc : e 1 ≠ 0 := by
      intro h
      exact one_ne_zero (e.injective (h.trans (map_zero e).symm))
    refine ⟨e 1, hc, ?_⟩
    ext x
    rw [he]
    change e (q₁ x) = e 1 * q₁ x
    have h := e.map_smul (q₁ x) (1 : L)
    simpa only [smul_eq_mul, mul_one, one_mul, mul_comm] using h
  · rintro ⟨c, hc, he⟩
    refine ⟨LinearEquiv.smulOfNeZero L L c hc, ?_⟩
    ext x
    rw [he]
    rfl

def surjectiveOneDimensionalQuotientSetoid (L M : Type u)
    [Field L] [AddCommGroup M] [Module L M] :
    Setoid {q : M →ₗ[L] L // Function.Surjective q} where
  r q₁ q₂ := OneDimensionalQuotientTargetIso q₁.1 q₂.1
  iseqv :=
    { refl := fun q => ⟨LinearEquiv.refl L L, by ext x; rfl⟩
      symm := by
        rintro q₁ q₂ ⟨e, he⟩
        refine ⟨e.symm, ?_⟩
        ext x
        rw [he]
        exact (e.symm_apply_apply (q₁.1 x)).symm
      trans := by
        rintro q₁ q₂ q₃ ⟨e₁₂, h₁₂⟩ ⟨e₂₃, h₂₃⟩
        refine ⟨e₁₂.trans e₂₃, ?_⟩
        ext x
        rw [h₂₃, h₁₂]
        rfl }

end PfaffianDescent
