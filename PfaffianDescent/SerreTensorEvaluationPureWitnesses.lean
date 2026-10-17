import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Surjective tensor evaluation transfers through actual witnesses for
every native one-tensor section value. -/
noncomputable section
open scoped TensorProduct
namespace PfaffianDescent
universe u

theorem serreTensorEvaluation_surjective_of_pure_tensor_witnesses
    {F E V U W Z : Type u} [Field F] [Field E] [Algebra F E]
    [AddCommGroup V] [Module F V] [AddCommGroup U] [Module E U]
    [AddCommGroup W] [Module E W] [AddCommGroup Z] [Module E Z]
    (old : E ⊗[F] V →ₗ[E] U) (honto : Function.Surjective old)
    (new : W →ₗ[E] Z) (coord : Z ≃ₗ[E] U)
    (hcol : ∀ v : V, ∃ w : W, coord (new w) = old (1 ⊗ₜ[F] v)) :
    Function.Surjective new := by
  have hw : ∀ t : E ⊗[F] V, ∃ w : W, coord (new w) = old t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by simp only [map_add, ha, hb]⟩
    | tmul c v =>
      obtain ⟨w, hw⟩ := hcol v
      refine ⟨c • w, ?_⟩
      have ht : c ⊗ₜ[F] v = c • (1 ⊗ₜ[F] v) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, new.map_smul, coord.map_smul, old.map_smul, hw]
  intro z
  obtain ⟨t, ht⟩ := honto (coord z)
  obtain ⟨w, hw⟩ := hw t
  exact ⟨w, coord.injective (hw.trans ht)⟩

end PfaffianDescent
