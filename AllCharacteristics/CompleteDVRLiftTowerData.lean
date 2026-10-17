import AllCharacteristics.CompleteDVRLiftData
import AllCharacteristics.FiniteExtensionDVRLifting

/-!
# Successor data for towers of complete DVR lifts

The Cohen-ring construction must make finite-extension lift choices
compatibly.  This file packages a lift with a chosen uniformizer and proves
that the finite-extension construction produces an injective,
residue-compatible successor map preserving that uniformizer.
-/

namespace AllCharacteristics

universe u

/-- A retained complete DVR lift with a specified irreducible uniformizer. -/
structure CompleteCharZeroDVRLiftWithUniformizer (k : Type u) [Field k] where
  lift : CompleteCharZeroDVRLiftData k
  uniformizer : lift.R
  uniformizer_irreducible : letI : CommRing lift.R := lift.commRing
    letI : IsDomain lift.R := lift.domain
    letI : IsDiscreteValuationRing lift.R := lift.dvr
    Irreducible uniformizer

namespace CompleteCharZeroDVRLiftWithUniformizer

/-- Choose a uniformizer for a retained complete DVR lift. -/
noncomputable def ofLiftData {k : Type u} [Field k]
    (D : CompleteCharZeroDVRLiftData k) :
    CompleteCharZeroDVRLiftWithUniformizer k :=
  Classical.choice (by
    have hdata : Nonempty (CompleteCharZeroDVRLiftWithUniformizer k) := by
      letI : CommRing D.R := D.commRing
      letI : IsDomain D.R := D.domain
      letI : IsDiscreteValuationRing D.R := D.dvr
      obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible D.R
      exact ⟨⟨D, t, ht⟩⟩
    exact hdata)

end CompleteCharZeroDVRLiftWithUniformizer

/-- An injective extension map between retained DVR lifts which commutes with
the prescribed residue maps and carries the selected uniformizer forward. -/
structure CompleteCharZeroDVRLiftUniformizerExtensionData
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (D : CompleteCharZeroDVRLiftWithUniformizer k) where
  target : CompleteCharZeroDVRLiftWithUniformizer L
  inclusion : letI : CommRing D.lift.R := D.lift.commRing
    letI : CommRing target.lift.R := target.lift.commRing
    D.lift.R →+* target.lift.R
  inclusion_injective : letI : CommRing D.lift.R := D.lift.commRing
    letI : CommRing target.lift.R := target.lift.commRing
    Function.Injective inclusion
  residue_commutes : letI : CommRing D.lift.R := D.lift.commRing
    letI : CommRing target.lift.R := target.lift.commRing
    ∀ r : D.lift.R, target.lift.residue (inclusion r) =
      algebraMap k L (D.lift.residue r)
  uniformizer_maps : letI : CommRing D.lift.R := D.lift.commRing
    letI : CommRing target.lift.R := target.lift.commRing
    inclusion D.uniformizer = target.uniformizer

namespace CompleteCharZeroDVRLiftUniformizerExtensionData

/-- The finite residue-field lifting construction gives the complete,
injective, uniformizer-preserving successor datum needed by a tower. -/
noncomputable def finiteExtension
    {k L : Type u} [Field k] [Field L] [Algebra k L] [Module.Finite k L]
    (D : CompleteCharZeroDVRLiftWithUniformizer k) :
    CompleteCharZeroDVRLiftUniformizerExtensionData (L := L) D :=
  Classical.choice (by
    have hdata : Nonempty (CompleteCharZeroDVRLiftUniformizerExtensionData (L := L) D) := by
      letI : CommRing D.lift.R := D.lift.commRing
      letI : IsDomain D.lift.R := D.lift.domain
      letI : IsDiscreteValuationRing D.lift.R := D.lift.dvr
      letI : IsAdicComplete (IsLocalRing.maximalIdeal D.lift.R) D.lift.R := D.lift.complete
      letI : CharZero D.lift.R := D.lift.charZero
      obtain ⟨A, commA, algRA, domA, dvrA, freeA, finiteA, completeA, charZeroA,
        c, hc, hcoef, hinj, htirr⟩ :=
        exists_completeDVR_lift_of_finite_extension_with_uniformizer
          (L := L) D.lift.residue D.lift.residue_surjective
          D.uniformizer D.uniformizer_irreducible
      letI : CommRing A := commA
      letI : Algebra D.lift.R A := algRA
      letI : IsDomain A := domA
      letI : IsDiscreteValuationRing A := dvrA
      letI : Module.Free D.lift.R A := freeA
      letI : Module.Finite D.lift.R A := finiteA
      letI : IsAdicComplete (IsLocalRing.maximalIdeal A) A := completeA
      letI : CharZero A := charZeroA
      let targetLift : CompleteCharZeroDVRLiftData L :=
        ⟨A, commA, domA, dvrA, completeA, charZeroA, c, hc⟩
      let target : CompleteCharZeroDVRLiftWithUniformizer L :=
        ⟨targetLift, algebraMap D.lift.R A D.uniformizer, htirr⟩
      exact ⟨⟨target, algebraMap D.lift.R A, hinj, hcoef, rfl⟩⟩
    exact hdata)

end CompleteCharZeroDVRLiftUniformizerExtensionData

end AllCharacteristics
