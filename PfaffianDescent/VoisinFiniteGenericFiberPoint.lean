import AllCharacteristics.ProjectiveConfigurationGenericPoint

/-! Uniqueness of the point over the generic point under a finite quotient. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace

universe u

/-- If an integral scheme maps finitely and surjectively to another integral
scheme, every point over the target's generic point is the source's generic
point. -/
theorem finiteSurjective_pointOverGeneric_eq_generic
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [Surjective f]
    (x : X) (hx : f x = genericPoint Y) :
    x = genericPoint X := by
  let c := Y.fromSpecStalk (genericPoint Y)
  let T := pullback f c
  let j : T ⟶ X := pullback.fst f c
  have hc : Set.range c = {genericPoint Y} := by
    rw [Scheme.range_fromSpecStalk]
    ext y
    change (y ⤳ genericPoint Y) ↔ y = genericPoint Y
    exact ⟨fun h => (h.antisymm
      ((genericPoint_spec Y).specializes (Set.mem_univ y))).eq,
      fun h => specializes_of_eq h⟩
  have hj : Set.range j = f ⁻¹' {genericPoint Y} := by
    change Set.range (pullback.fst f c) = _
    rw [Scheme.Pullback.range_fst, hc]
  obtain ⟨g, hg⟩ : genericPoint X ∈ Set.range j := by
    rw [hj]
    exact AllCharacteristics.genericPoint_map_of_surjective f
  obtain ⟨w, hw⟩ : x ∈ Set.range j := by
    rw [hj]
    exact hx
  letI : Subsingleton T :=
    (AllCharacteristics.genericPullback_nonempty_subsingleton_of_irreducible f).2
  exact hw.symm.trans ((congrArg j (Subsingleton.elim w g)).trans hg)

end PfaffianDescent
