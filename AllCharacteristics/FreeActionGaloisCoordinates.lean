import AllCharacteristics.FreeActionTensorKernels
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-! # Finite Galois coordinates from actual no-fixed-locus ideals -/

open scoped TensorProduct
namespace AllCharacteristics
universe u v
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (G : Type v) [Group G] [Finite G] [DecidableEq G]
variable [MulSemiringAction G B] [SMulCommClass G R B]

include R in
/-- Scheme-theoretic freeness supplies a finite tensor expression that evaluates
to one at the identity and zero at every other group component. -/
theorem exists_freeAction_galois_coordinates
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    ∃ (n : ℕ) (a b : Fin n → B),
      ∀ g : G, (∑ i, a i * (g • b i)) = if g = 1 then 1 else 0 := by
  obtain ⟨t, ht⟩ := invariantTensorEvaluation_pi_surjective R B G hfree
    (fun g ↦ if g = 1 then 1 else 0)
  obtain ⟨n, a, b, he⟩ := TensorProduct.exists_sum_tmul_eq t
  refine ⟨n, a, b, fun g ↦ ?_⟩
  have hg := congrFun ht g
  change invariantTensorEvaluation R B G g t = _ at hg
  rw [he, map_sum] at hg
  exact hg

end AllCharacteristics
