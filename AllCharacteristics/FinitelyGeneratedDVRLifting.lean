import AllCharacteristics.CompleteDVRLiftingBase
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.Finite.Basic

/-!
# Complete DVR lifts of finitely generated field extensions

Choose a transcendence basis, construct a lift of its rational function
field, and extend that lift through the remaining finite extension. The
remaining extension is finite because the original field extension is
finitely generated. No separability or perfectness is needed for this step.
-/

namespace AllCharacteristics
universe u

/-- A constructed lifting base extends to every finitely generated field
extension. The transcendence basis and its finite residual extension are
constructed inside the proof. -/
theorem HasCompleteCharZeroDVRLift.essFiniteType
    {F E : Type u} [Field F] [Field E] [Algebra F E] [Algebra.EssFiniteType F E]
    (h : HasCompleteCharZeroDVRLift F) : HasCompleteCharZeroDVRLift E := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F E
  let K := IntermediateField.adjoin F (Set.range (Subtype.val : s → E))
  have : Algebra.IsAlgebraic K E := hs.isAlgebraic_field
  have : Algebra.EssFiniteType K E := Algebra.EssFiniteType.of_comp F K E
  have : Module.Finite K E := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have hK : HasCompleteCharZeroDVRLift K :=
    (h.rationalFunction s).of_equiv hs.1.aevalEquivField.toRingEquiv
  exact hK.finite_extension

/-- Every finitely generated extension of a perfect field of positive
characteristic admits an actual complete characteristic-zero DVR lift,
including imperfect extensions. -/
theorem hasCompleteCharZeroDVRLift_of_essFiniteType_perfect_positive
    (p : ℕ) [Fact p.Prime] (F E : Type u) [Field F] [Field E]
    [CharP F p] [PerfectRing F p] [Algebra F E] [Algebra.EssFiniteType F E] :
    HasCompleteCharZeroDVRLift E :=
  (hasCompleteCharZeroDVRLift_of_perfect_positive p F).essFiniteType

/-- The prime subfield in positive characteristic is finite. -/
theorem primeSubfield_finite_positive
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] :
    Finite (⊥ : Subfield k) := by
  have hf : Finite (ZMod.castHom (m := p) dvd_rfl k).fieldRange :=
    Finite.of_surjective _ (ZMod.castHom (m := p) dvd_rfl k).rangeRestrictField_bijective.2
  simpa only [ZMod.fieldRange_castHom_eq_bot] using hf

/-- Every finitely generated field of positive characteristic admits a
constructed complete characteristic-zero DVR with that exact residue field. -/
theorem hasCompleteCharZeroDVRLift_of_fg_positive
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [Field.FG k] :
    HasCompleteCharZeroDVRLift k := by
  have : Finite (⊥ : Subfield k) := primeSubfield_finite_positive p k
  have : Algebra.EssFiniteType (⊥ : Subfield k) k := Field.fg_iff_essFiniteType.mp inferInstance
  exact hasCompleteCharZeroDVRLift_of_essFiniteType_perfect_positive p (⊥ : Subfield k) k

end AllCharacteristics
