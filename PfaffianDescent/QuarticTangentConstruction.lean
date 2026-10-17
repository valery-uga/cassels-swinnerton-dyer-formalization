import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The linear choice in the length-eight tangent construction

Proposition 5.5 of `2-proofs.tex` begins with a six-dimensional space of
quadrics mapping into an eight-dimensional cotangent space.  The elementary
dual-annihilator argument here supplies the nonzero functional used there.
-/

namespace PfaffianDescent
namespace QuarticNet

section
variable {K V E : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- A linear map into a strictly larger finite-dimensional space has a
nonzero dual functional that annihilates its image. -/
theorem exists_nonzero_dual_annihilating_of_finrank_lt
    (φ : V →ₗ[K] E) (hsize : Module.finrank K V < Module.finrank K E) :
    ∃ ell : Module.Dual K E, ell ≠ 0 ∧ ∀ v : V, ell (φ v) = 0 := by
  have hrange : Module.finrank K (LinearMap.range φ) < Module.finrank K E :=
    lt_of_le_of_lt (LinearMap.finrank_range_le φ) hsize
  have hannpos : 0 < Module.finrank K (LinearMap.range φ).dualAnnihilator := by
    have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range φ)
    omega
  have hann : (LinearMap.range φ).dualAnnihilator ≠ ⊥ := by
    intro he
    have hz : Module.finrank K (LinearMap.range φ).dualAnnihilator = 0 := by
      rw [he]
      simp
    omega
  obtain ⟨ell, hell, hell0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hann
  refine ⟨ell, hell0, ?_⟩
  intro v
  exact (Submodule.mem_dualAnnihilator ell).mp hell (φ v) ⟨v, rfl⟩

/-- The numerical `6 → 8` instance used for the map from quadrics through a
degree-four point to its twisted cotangent space. -/
theorem exists_nonzero_dual_annihilating_six_to_eight
    (φ : (Fin 6 → K) →ₗ[K] (Fin 8 → K)) :
    ∃ ell : Module.Dual K (Fin 8 → K), ell ≠ 0 ∧ ∀ v : Fin 6 → K, ell (φ v) = 0 := by
  apply exists_nonzero_dual_annihilating_of_finrank_lt φ
  simp

end
end QuarticNet
end PfaffianDescent
