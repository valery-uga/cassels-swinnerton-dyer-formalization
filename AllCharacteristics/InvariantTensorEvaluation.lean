import AllCharacteristics.AffineInvariantQuotient
import Mathlib.RingTheory.TensorProduct.Maps

/-! # The actual tensor evaluation maps for a finite-group quotient -/

open scoped TensorProduct
namespace AllCharacteristics
universe u v
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (G : Type v) [Group G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- Every action automorphism is linear over the actual fixed subalgebra. -/
noncomputable def invariantActionAlgHom (g : G) :
    B →ₐ[FixedPoints.subalgebra R B G] B where
  toRingHom := MulSemiringAction.toRingHom G B g
  commutes' a := a.property g

/-- Evaluation at a group element on the actual tensor square over the invariant ring. -/
noncomputable def invariantTensorEvaluation (g : G) :
    B ⊗[FixedPoints.subalgebra R B G] B →ₐ[B] B :=
  Algebra.TensorProduct.lift (AlgHom.id B B) (invariantActionAlgHom R B G g)
    (fun _ _ ↦ Commute.all _ _)

/-- Evaluation on a pure tensor has the usual orbit formula. -/
theorem invariantTensorEvaluation_tmul (g : G) (a b : B) :
    invariantTensorEvaluation R B G g (a ⊗ₜ[FixedPoints.subalgebra R B G] b) = a * (g • b) := rfl

/-- Each tensor evaluation is surjective through the first tensor factor. -/
theorem invariantTensorEvaluation_surjective (g : G) :
    Function.Surjective (invariantTensorEvaluation R B G g) := by
  intro b
  refine ⟨b ⊗ₜ 1, ?_⟩
  rw [invariantTensorEvaluation_tmul, smul_one, mul_one]

end AllCharacteristics
