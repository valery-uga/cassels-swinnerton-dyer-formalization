import PfaffianDescent.SignedCyclePushforward

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory AllCharacteristics
universe u
section
variable {X Y : Scheme.{u}}

lemma effectiveCycleToSigned_add (z w : EffectiveZeroCycle X) :
    (z + w).toZeroCycle = z.toZeroCycle + w.toZeroCycle := by
  ext x
  exact Nat.cast_add (z x) (w x)

lemma effectiveCycleToSigned_nsmul (n : ℕ) (z : EffectiveZeroCycle X) :
    (n • z).toZeroCycle = n • z.toZeroCycle := by
  induction n with
  | zero => simp [EffectiveZeroCycle.toZeroCycle]
  | succ n ih =>
      rw [succ_nsmul, succ_nsmul, effectiveCycleToSigned_add, ih]

lemma effectiveCycleToSigned_single (x : closedPoints X) (n : ℕ) :
    EffectiveZeroCycle.toZeroCycle (Finsupp.single x n : EffectiveZeroCycle X) =
      Finsupp.single x (n : ℤ) :=
  Finsupp.mapRange_single

lemma effectiveCyclePushforward_add (f : X ⟶ Y) [UniversallyClosed f] (z w : EffectiveZeroCycle X) :
    pushforwardCycle f (z + w) = pushforwardCycle f z + pushforwardCycle f w := by
  classical
  exact Finsupp.sum_add_index' (fun x => by simp)
    (fun x n m => by simp only [add_mul, Finsupp.single_add])

lemma effectiveCyclePushforward_single (f : X ⟶ Y) [UniversallyClosed f] (x : closedPoints X) (n : ℕ) :
    pushforwardCycle f (Finsupp.single x n) =
      Finsupp.single (universallyClosedPointMap f x) (n * f.residueDegree x.val) := by
  exact Finsupp.sum_single_index (by simp)

/-- Passing from effective to signed cycles commutes with the actual residue-weighted pushforward. -/
theorem signedCyclePushforward_effective (f : X ⟶ Y) [UniversallyClosed f] (z : EffectiveZeroCycle X) :
    signedCyclePushforward f z.toZeroCycle = (pushforwardCycle f z).toZeroCycle := by
  classical
  induction z using Finsupp.induction with
  | zero => simp [EffectiveZeroCycle.toZeroCycle, pushforwardCycle]
  | @single_add x n z hx hn ih =>
      rw [effectiveCycleToSigned_add, map_add, effectiveCyclePushforward_add,
        effectiveCycleToSigned_add, ih, effectiveCycleToSigned_single,
        signedCyclePushforward_single, effectiveCyclePushforward_single, effectiveCycleToSigned_single,
        Nat.cast_mul]

end
end PfaffianDescent
