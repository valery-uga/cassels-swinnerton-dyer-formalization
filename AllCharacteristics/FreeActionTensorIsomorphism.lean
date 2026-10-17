import AllCharacteristics.FreeActionFiniteProjective
import Mathlib.Algebra.Algebra.Pi

/-! # The actual tensor-square isomorphism for a free finite-group action -/

open scoped TensorProduct
namespace AllCharacteristics
universe u v
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (G : Type v) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- The orbit-trace dual generators reconstruct every tensor from its group evaluations. -/
theorem invariantTensorEvaluation_reconstruction [DecidableEq G] {n : ℕ} (a b : Fin n → B)
    (hc : ∀ g : G, (∑ i, a i * (g • b i)) = if g = 1 then 1 else 0)
    (t : B ⊗[FixedPoints.subalgebra R B G] B) :
    t = ∑ i, (∑ g : G, invariantTensorEvaluation R B G g t * (g • b i)) ⊗ₜ a i := by
  classical
  induction t with
  | zero => simp only [map_zero, zero_mul, Finset.sum_const_zero, TensorProduct.zero_tmul]
  | tmul x y =>
    calc
      x ⊗ₜ[FixedPoints.subalgebra R B G] y =
          x ⊗ₜ (∑ i, (invariantOrbitTrace R B G (b i * y)) • a i) := by
        rw [invariantOrbitTrace_dual_generators R B G a b hc y]
      _ = ∑ i, (x * (invariantOrbitTrace R B G (b i * y)).val) ⊗ₜ a i := by
        rw [TensorProduct.tmul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [TensorProduct.tmul_smul]
        apply congrArg (fun z : B ↦ z ⊗ₜ[FixedPoints.subalgebra R B G] a i)
        change (invariantOrbitTrace R B G (b i * y)).val * x =
          x * (invariantOrbitTrace R B G (b i * y)).val
        exact mul_comm _ _
      _ = ∑ i, (∑ g : G, invariantTensorEvaluation R B G g (x ⊗ₜ y) * (g • b i)) ⊗ₜ a i := by
        apply Finset.sum_congr rfl
        intro i _
        apply congrArg (fun z : B ↦ z ⊗ₜ[FixedPoints.subalgebra R B G] a i)
        rw [invariantOrbitTrace_val, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        rw [smul_mul', invariantTensorEvaluation_tmul]
        ring
  | add x y hx hy =>
    simp only [map_add, add_mul, Finset.sum_add_distrib, TensorProduct.add_tmul]
    rw [← hx, ← hy]

/-- Under the actual free-action ideal condition the tensor evaluations are jointly injective. -/
theorem invariantTensorEvaluation_pi_injective
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    Function.Injective (fun t g ↦ invariantTensorEvaluation R B G g t) := by
  classical
  obtain ⟨n, a, b, hc⟩ := exists_freeAction_galois_coordinates R B G hfree
  intro x y hxy
  calc
    x = ∑ i, (∑ g : G, invariantTensorEvaluation R B G g x * (g • b i)) ⊗ₜ a i :=
      invariantTensorEvaluation_reconstruction R B G a b hc x
    _ = ∑ i, (∑ g : G, invariantTensorEvaluation R B G g y * (g • b i)) ⊗ₜ a i := by
      simp_rw [show ∀ g, invariantTensorEvaluation R B G g x =
        invariantTensorEvaluation R B G g y from fun g ↦ congrFun hxy g]
    _ = y := (invariantTensorEvaluation_reconstruction R B G a b hc y).symm

/-- The tensor square of the actual invariant quotient is the product indexed by the original group. -/
noncomputable def freeActionTensorAlgEquiv
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    B ⊗[FixedPoints.subalgebra R B G] B ≃ₐ[B] (G → B) :=
  AlgEquiv.ofBijective (AlgHom.pi (invariantTensorEvaluation R B G))
    ⟨invariantTensorEvaluation_pi_injective R B G hfree,
      invariantTensorEvaluation_pi_surjective R B G hfree⟩

/-- The constructed tensor-square isomorphism is the original group-evaluation map. -/
theorem freeActionTensorAlgEquiv_apply
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤)
    (t : B ⊗[FixedPoints.subalgebra R B G] B) (g : G) :
    freeActionTensorAlgEquiv R B G hfree t g = invariantTensorEvaluation R B G g t := rfl

end AllCharacteristics
