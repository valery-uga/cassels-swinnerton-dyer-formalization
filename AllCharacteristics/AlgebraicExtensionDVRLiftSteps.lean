import AllCharacteristics.AlgebraicExtensionTransfiniteFiltration
import AllCharacteristics.CompleteDVRLiftTowerData

/-!
# Successor steps in an algebraic DVR-lift tower

The field filtration has finite steps.  Applying the finite-extension DVR
constructor at each such step produces the successor datum used by the
transfinite Cohen-ring construction.
-/

namespace AllCharacteristics

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The field at a minimal filtration stage is the original base field. -/
theorem transfiniteStageField_eq_bot_of_isMin {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) (ha : IsMin a) :
    transfiniteStageField (K := K) e a = ⊥ := by
  rw [transfiniteStageField]
  have hIio : Set.Iio a = ∅ := by
    apply Set.Subset.antisymm
    · intro x hx
      exact (ha.not_lt hx).elim
    · exact Set.empty_subset _
  rw [hIio, Set.image_empty]
  exact IntermediateField.adjoin_empty K L

/-- A complete DVR lift of the original base field supplies the retained
lift at any minimal stage of the filtration. -/
noncomputable def transfiniteStageLiftMin {ι : Type u} [LinearOrder ι]
    (e : ι → L) (a : ι) (ha : IsMin a)
    (hK : HasCompleteCharZeroDVRLift K) :
    CompleteCharZeroDVRLiftWithUniformizer (transfiniteStageField (K := K) e a) := by
  let D : CompleteCharZeroDVRLiftWithUniformizer (⊥ : IntermediateField K L) :=
    CompleteCharZeroDVRLiftWithUniformizer.ofLiftData
      (CompleteCharZeroDVRLiftData.ofHasCompleteCharZeroDVRLift
        (hK.of_equiv (IntermediateField.botEquiv K L).symm.toRingEquiv))
  rw [transfiniteStageField_eq_bot_of_isMin e a ha]
  exact D

/-- The finite-extension constructor for complete DVR lifts applies at each
successor of an algebraic transfinite field filtration. -/
noncomputable def transfiniteStageLiftSuccessor {ι : Type u}
    [LinearOrder ι] [SuccOrder ι] [Algebra.IsAlgebraic K L]
    (e : ι → L) (a : ι) (ha : ¬ IsMax a)
    (D : CompleteCharZeroDVRLiftWithUniformizer
      (transfiniteStageField (K := K) e a)) :
    let E := transfiniteStageField (K := K) e a
    let F := transfiniteStageField (K := K) e (Order.succ a)
    let _ : Algebra E F :=
      (IntermediateField.inclusion
        (transfiniteStageField_mono e (Order.le_succ a))).toRingHom.toAlgebra
    CompleteCharZeroDVRLiftUniformizerExtensionData (L := F) D := by
  let E := transfiniteStageField (K := K) e a
  let F := transfiniteStageField (K := K) e (Order.succ a)
  have hEF : E ≤ F := transfiniteStageField_mono e (Order.le_succ a)
  letI : Algebra E F := (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  letI : FiniteDimensional E F := transfiniteStageField_finiteDimensional_succ e a ha
  exact CompleteCharZeroDVRLiftUniformizerExtensionData.finiteExtension D

end AllCharacteristics
