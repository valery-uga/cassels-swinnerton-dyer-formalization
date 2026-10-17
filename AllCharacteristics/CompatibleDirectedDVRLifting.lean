import AllCharacteristics.CompleteDVRLiftingBase
import AllCharacteristics.DVRDirectedColimit

/-!
# Completing compatible directed systems of DVR lifts

This is the final formal reduction at a limit stage of the Cohen-ring
construction.  A compatible system supplies a generally noncomplete DVR by a
directed colimit; completing it preserves the collectively specified residue
field.
-/

namespace AllCharacteristics

universe u

/-- A compatible directed system of characteristic-zero DVR lifts, with
collectively surjective residue maps, yields a complete characteristic-zero
DVR lift. -/
theorem hasCompleteCharZeroDVRLift_of_compatibleDirectedDVRSystem
    {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (A : ι → Type u) [∀ i, CommRing (A i)]
    (f : ∀ i j (_ : i ≤ j), A i →+* A j)
    [DirectedSystem A (f · · ·)]
    [∀ i, IsDomain (A i)] [∀ i, IsDiscreteValuationRing (A i)]
    [∀ i, CharZero (A i)]
    (π : ∀ i, A i)
    (hπ : ∀ i, Irreducible (π i))
    (hπmap : ∀ i j (h : i ≤ j), f i j h (π i) = π j)
    (hinj : ∀ i j (h : i ≤ j), Function.Injective (f i j h))
    {L : Type u} [Field L]
    (b : ∀ i, A i →+* L)
    (hcompat : ∀ i j (h : i ≤ j) (x : A i), b j (f i j h x) = b i x)
    (hsurj : ∀ x : L, ∃ (i : ι) (y : A i), b i y = x)
    (i₀ : ι) :
    HasCompleteCharZeroDVRLift L := by
  letI : IsDomain (DirectLimit A f) := directLimit_isDomain_of_injective A f hinj
  letI : IsDiscreteValuationRing (DirectLimit A f) :=
    directLimit_isDiscreteValuationRing_of_injective_uniformizers A f π hπ hπmap hinj i₀
  have hofinj : Function.Injective (DirectLimit.Ring.of A f i₀) :=
    DirectLimit.mk_injective f hinj i₀
  letI : CharZero (DirectLimit A f) :=
    charZero_of_injective_ringHom hofinj
  let b' := DirectLimit.Ring.lift A f L b hcompat
  have hb' : Function.Surjective b' := by
    intro x
    obtain ⟨i, y, hy⟩ := hsurj x
    refine ⟨DirectLimit.Ring.of A f i y, ?_⟩
    rw [show b' = DirectLimit.Ring.lift A f L b hcompat from rfl,
      DirectLimit.Ring.lift_of]
    exact hy
  obtain ⟨R, _, _, _, _, _, _, c, hc, _⟩ :=
    exists_completeDVR_of_DVR_residue b' hb'
  exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, c, hc⟩

end AllCharacteristics
