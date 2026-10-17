import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.Pi

/-! # Finite projectivity from a proved dual-generator identity -/

namespace AllCharacteristics
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- A finite dual-generator identity realizes the module as a direct summand
of an actual finite free module. -/
theorem finite_projective_of_dual_generators {n : ℕ} (a : Fin n → M)
    (ℓ : Fin n → M →ₗ[R] R) (h : ∀ x : M, (∑ i, ℓ i x • a i) = x) :
    Module.Finite R M ∧ Module.Projective R M := by
  classical
  let j : M →ₗ[R] (Fin n → R) := LinearMap.pi ℓ
  let s : (Fin n → R) →ₗ[R] M :=
    ∑ i, (LinearMap.id.smulRight (a i)).comp (LinearMap.proj i)
  have hs : ∀ x : M, s (j x) = x := by
    intro x
    simpa only [s, j, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.smulRight_apply, LinearMap.id_apply, LinearMap.proj_apply,
      LinearMap.pi_apply] using h x
  have hsj : s.comp j = LinearMap.id := LinearMap.ext hs
  exact ⟨Module.Finite.of_surjective s (fun x ↦ ⟨j x, hs x⟩),
    Module.Projective.of_split j s hsj⟩

end AllCharacteristics
