import AllCharacteristics.CyclePushforward
import AllCharacteristics.ProperCyclePushforward

/-!
# Effective-cycle pushforward along closed immersions

A closed immersion is an isomorphism on residue fields.  Consequently, the
residue-weighted proper pushforward of an effective cycle agrees with the
ordinary closed-subscheme pushforward.
-/

open AlgebraicGeometry CategoryTheory

namespace AllCharacteristics

universe u

/-- A closed immersion has residue degree one at every source point. -/
theorem residueDegree_one_of_isClosedImmersion
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i] (x : X) :
    i.residueDegree x = 1 := by
  letI : IsIso (i.residueFieldMap x) :=
    isIso_residueFieldMap_of_surjectiveOnStalks i x
  letI := (i.residueFieldMap x).hom.toAlgebra
  unfold Scheme.Hom.residueDegree
  apply Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
  change Function.Bijective (i.residueFieldMap x).hom
  exact ConcreteCategory.bijective_of_isIso _

/-- For a closed immersion, residue-weighted proper pushforward is the same
as the closed-subscheme cycle pushforward. -/
theorem pushforwardCycle_eq_pushforwardClosedCycle
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsClosedImmersion i]
    (z : EffectiveZeroCycle X) :
    pushforwardCycle i z = pushforwardClosedCycle i z := by
  classical
  have hdegree : ∀ x : closedPoints X, i.residueDegree x.1 = 1 := by
    intro x
    exact residueDegree_one_of_isClosedImmersion i x.1
  induction z using Finsupp.induction with
  | zero => simp [pushforwardCycle, pushforwardClosedCycle]
  | @single_add x n z hx hn hrec =>
      rw [show pushforwardCycle i (Finsupp.single x n + z) =
        pushforwardCycle i (Finsupp.single x n) + pushforwardCycle i z by
          exact Finsupp.sum_add_index' (fun x => by simp)
            (fun x n m => by simp only [add_mul, Finsupp.single_add])]
      rw [show pushforwardClosedCycle i (Finsupp.single x n + z) =
        pushforwardClosedCycle i (Finsupp.single x n) + pushforwardClosedCycle i z by
          unfold pushforwardClosedCycle
          rw [Finsupp.mapDomain_add]]
      rw [hrec]
      have hpush : pushforwardCycle i (Finsupp.single x n) =
          Finsupp.single (universallyClosedPointMap i x) (n * i.residueDegree x.1) := by
        unfold pushforwardCycle
        exact Finsupp.sum_single_index (by simp)
      rw [hpush, hdegree]
      have hpoint : universallyClosedPointMap i x = closedPointMap i x := by
        apply Subtype.ext
        rfl
      rw [hpoint]
      unfold pushforwardClosedCycle
      simp

end AllCharacteristics
