import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Chinese remainder surjectivity for actual ring maps -/

namespace AllCharacteristics
universe u v w
variable {T : Type u} [CommRing T] {B : Type v} [CommRing B]
variable {ι : Type w} [Finite ι]

/-- Surjective ring maps with pairwise comaximal kernels are jointly surjective. -/
theorem ringHom_pi_surjective_of_coprime_kernels (φ : ι → T →+* B)
    (hφ : ∀ i, Function.Surjective (φ i))
    (hker : Pairwise (fun i j ↦ IsCoprime (RingHom.ker (φ i)) (RingHom.ker (φ j)))) :
    Function.Surjective (fun t i ↦ φ i t) := by
  classical
  intro y
  choose z hz using fun i ↦ hφ i (y i)
  obtain ⟨t, ht⟩ := Ideal.exists_forall_sub_mem_ideal hker z
  refine ⟨t, funext fun i ↦ ?_⟩
  have h : φ i (t - z i) = 0 := ht i
  rw [map_sub, hz i, sub_eq_zero] at h
  exact h

end AllCharacteristics
