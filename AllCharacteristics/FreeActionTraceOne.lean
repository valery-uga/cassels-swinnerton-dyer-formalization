import AllCharacteristics.FreeActionEtale

/-!
# A trace-one element for an actual free finite-group invariant extension

The Galois dual-generator identity makes the extended trace ideal the unit
ideal. Faithful flatness contracts this identity back to the invariant ring.
This produces a trace-one element without dividing by the group order.
-/

namespace AllCharacteristics
universe u v
variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
variable (G : Type v) [Group G] [Fintype G] [MulSemiringAction G B] [SMulCommClass G R B]

/-- A scheme-theoretically free finite-group action has an element whose
actual orbit trace is one, even when the characteristic divides the group order. -/
theorem exists_invariantOrbitTrace_eq_one
    (hfree : ∀ g : G, g ≠ 1 → actionDifferenceIdeal B G g = ⊤) :
    ∃ b : B, invariantOrbitTrace R B G b = 1 := by
  classical
  let I := FixedPoints.subalgebra R B G
  have : Module.FaithfullyFlat I B := faithfullyFlat_fixedSubalgebra_of_free_action R B G hfree
  let J : Ideal I := LinearMap.range (invariantOrbitTrace R B G)
  obtain ⟨n, a, b, hc⟩ := exists_freeAction_galois_coordinates R B G hfree
  have hm : (1 : B) ∈ J.map (algebraMap I B) := by
    rw [← invariantOrbitTrace_dual_generators R B G a b hc (1 : B)]
    apply Ideal.sum_mem
    intro i _
    change (algebraMap I B (invariantOrbitTrace R B G (b i * 1))) * a i ∈ _
    apply Ideal.mul_mem_right
    exact Ideal.mem_map_of_mem _ (show invariantOrbitTrace R B G (b i * 1) ∈ J from ⟨b i * 1, rfl⟩)
  have h1 : (1 : I) ∈ J := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) J]
    change algebraMap I B 1 ∈ J.map (algebraMap I B)
    rw [map_one]
    exact hm
  exact h1

end AllCharacteristics
