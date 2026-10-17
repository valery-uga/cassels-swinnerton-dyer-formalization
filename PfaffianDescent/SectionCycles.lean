import AllCharacteristics.CyclePushforward

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

/-- A section over a field supplies an effective cycle of any prescribed degree. -/
theorem effective_cycle_of_section {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ X) (hs : s ≫ f = 𝟙 _) (n : ℕ) :
    ∃ z : AllCharacteristics.EffectiveZeroCycle X,
      AllCharacteristics.EffectiveZeroCycle.degree f z = n := by
  have : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id f s hs
  let x : closedPoints (Spec (.of K)) := ⟨IsLocalRing.closedPoint K, isClosed_singleton⟩
  refine ⟨AllCharacteristics.pushforwardClosedCycle s (Finsupp.single x n), ?_⟩
  rw [AllCharacteristics.degree_pushforwardClosedCycle, hs]
  simp [AllCharacteristics.EffectiveZeroCycle.degree]

end PfaffianDescent
