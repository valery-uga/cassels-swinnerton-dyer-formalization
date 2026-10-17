import AllCharacteristics.InvariantTensorEvaluation
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Basic

/-! # Orbit trace and finite dual generators over the invariant subalgebra -/

namespace AllCharacteristics
universe u v
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (G : Type v) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- Summing the orbit gives an actual invariant-valued linear map, without division by the order. -/
noncomputable def invariantOrbitTrace : B →ₗ[FixedPoints.subalgebra R B G]
    FixedPoints.subalgebra R B G where
  toFun b := ⟨∑ g : G, g • b, by
    intro h
    rw [Finset.smul_sum]
    simp only [← mul_smul]
    exact Equiv.sum_comp (Equiv.mulLeft h) (fun g : G ↦ g • b)⟩
  map_add' a b := by
    apply Subtype.ext
    change (∑ g : G, g • (a + b)) = (∑ g : G, g • a) + ∑ g : G, g • b
    simp only [smul_add, Finset.sum_add_distrib]
  map_smul' a b := by
    apply Subtype.ext
    change (∑ g : G, g • (a.val * b)) = a.val * ∑ g : G, g • b
    simp only [smul_mul', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    rw [show g • a.val = a.val from a.property g]

/-- The orbit trace is the sum of the original group action in the original ring. -/
theorem invariantOrbitTrace_val (b : B) :
    (invariantOrbitTrace R B G b).val = ∑ g : G, g • b := rfl

/-- A tensor separating the identity component gives an explicit finite dual-generator formula. -/
theorem invariantOrbitTrace_dual_generators [DecidableEq G] {n : ℕ} (a b : Fin n → B)
    (hcoord : ∀ g : G, (∑ i, a i * (g • b i)) = if g = 1 then 1 else 0) (x : B) :
    (∑ i, (invariantOrbitTrace R B G (b i * x)) • a i) = x := by
  classical
  change (∑ i, (∑ g : G, g • (b i * x)) * a i) = x
  calc
    (∑ i, (∑ g : G, g • (b i * x)) * a i) =
        ∑ g : G, (∑ i, a i * (g • b i)) * (g • x) := by
      simp only [smul_mul', Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = x := by simp_rw [hcoord]; simp

end AllCharacteristics
