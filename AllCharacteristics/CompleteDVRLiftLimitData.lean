import AllCharacteristics.CompleteDVRLiftTowerData
import AllCharacteristics.DVRDirectedColimit
import AllCharacteristics.DVRCompletion

/-!
# Limit data for towers of complete DVR lifts

At a limit stage, a compatible directed system of DVR lifts is first
colimited and then completed.  This file retains the resulting complete lift,
the maps from all earlier stages, the residue compatibility, and the chosen
uniformizer.
-/

namespace AllCharacteristics

universe u

/-- The retained output of completing a compatible directed system of DVR
lifts. -/
structure CompleteCharZeroDVRLiftUniformizerLimitData
    {ι : Type u} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
    (A : ι → Type u) [∀ i, CommRing (A i)]
    (f : ∀ i j (_ : i ≤ j), A i →+* A j)
    [DirectedSystem A (f · · ·)]
    (π : ∀ i, A i)
    {L : Type u} [Field L]
    (b : ∀ i, A i →+* L)
    (i₀ : ι) where
  target : CompleteCharZeroDVRLiftWithUniformizer L
  inclusion : letI : CommRing target.lift.R := target.lift.commRing
    DirectLimit A f →+* target.lift.R
  inclusion_injective : letI : CommRing target.lift.R := target.lift.commRing
    Function.Injective inclusion
  residue_commutes : letI : CommRing target.lift.R := target.lift.commRing
    ∀ (i : ι) (x : A i),
      target.lift.residue (inclusion (DirectLimit.Ring.of A f i x)) = b i x
  uniformizer_maps : letI : CommRing target.lift.R := target.lift.commRing
    inclusion (directLimitUniformizer A f i₀ π) = target.uniformizer

namespace CompleteCharZeroDVRLiftUniformizerLimitData

/-- Complete a compatible directed system while retaining all maps and the
uniformizer used by the next tower stage. -/
noncomputable def ofCompatibleDirectedSystem
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
    CompleteCharZeroDVRLiftUniformizerLimitData A f π b i₀ := by
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
  let R := AdicCompletion (IsLocalRing.maximalIdeal (DirectLimit A f)) (DirectLimit A f)
  let c : R →+* L := dvrCompletionResidueMap b' hb'
  have hc : Function.Surjective c := dvrCompletionResidueMap_surjective b' hb'
  let targetLift : CompleteCharZeroDVRLiftData L :=
    ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
      dvrCompletion_charZero, c, hc⟩
  let target : CompleteCharZeroDVRLiftWithUniformizer L :=
    ⟨targetLift,
      algebraMap (DirectLimit A f) R (directLimitUniformizer A f i₀ π),
      dvrCompletion_uniformizer_irreducible _
        (directLimitUniformizer_irreducible A f π hπ hπmap hinj i₀)⟩
  refine ⟨target, algebraMap (DirectLimit A f) R,
    dvrCompletion_algebraMap_injective, ?_, ?_⟩
  · intro i x
    change c (algebraMap (DirectLimit A f) R (DirectLimit.Ring.of A f i x)) = b i x
    rw [dvrCompletionResidueMap_algebraMap b' hb',
      show b' = DirectLimit.Ring.lift A f L b hcompat from rfl,
      DirectLimit.Ring.lift_of]
  · rfl

end CompleteCharZeroDVRLiftUniformizerLimitData

end AllCharacteristics
