import AllCharacteristics.CompleteDVRLiftingBase

/-!
# Data for complete characteristic-zero DVR lifts

`HasCompleteCharZeroDVRLift` is deliberately an existence proposition.  The
transfinite Cohen-ring construction also needs to retain the ring and its
residue map so that successive and limit-stage maps can be recorded.  This
structure packages that data while remaining equivalent to the existence
proposition.
-/

namespace AllCharacteristics

universe u

/-- A complete characteristic-zero DVR together with a specified surjective
residue map to a field. -/
structure CompleteCharZeroDVRLiftData (k : Type u) [Field k] where
  R : Type u
  commRing : CommRing R
  domain : letI : CommRing R := commRing; IsDomain R
  dvr : letI : CommRing R := commRing
    letI : IsDomain R := domain
    IsDiscreteValuationRing R
  complete : letI : CommRing R := commRing
    letI : IsDomain R := domain
    letI : IsDiscreteValuationRing R := dvr
    IsAdicComplete (IsLocalRing.maximalIdeal R) R
  charZero : letI : CommRing R := commRing; CharZero R
  residue : letI : CommRing R := commRing; R →+* k
  residue_surjective : Function.Surjective residue

namespace CompleteCharZeroDVRLiftData

/-- Forgetting the chosen presentation gives the existing lift-existence
proposition. -/
theorem hasCompleteCharZeroDVRLift {k : Type u} [Field k]
    (D : CompleteCharZeroDVRLiftData k) :
    HasCompleteCharZeroDVRLift k := by
  letI : CommRing D.R := D.commRing
  letI : IsDomain D.R := D.domain
  letI : IsDiscreteValuationRing D.R := D.dvr
  letI : IsAdicComplete (IsLocalRing.maximalIdeal D.R) D.R := D.complete
  letI : CharZero D.R := D.charZero
  exact ⟨D.R, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, D.residue, D.residue_surjective⟩

/-- Classical choice turns any existing lift into retained data. -/
noncomputable def ofHasCompleteCharZeroDVRLift {k : Type u} [Field k]
    (h : HasCompleteCharZeroDVRLift k) :
    CompleteCharZeroDVRLiftData k :=
  Classical.choice (by
    have hdata : Nonempty (CompleteCharZeroDVRLiftData k) := by
      obtain ⟨R, comm, dom, dvr, complete, cz, b, hb⟩ := h
      letI : CommRing R := comm
      letI : IsDomain R := dom
      letI : IsDiscreteValuationRing R := dvr
      letI : IsAdicComplete (IsLocalRing.maximalIdeal R) R := complete
      letI : CharZero R := cz
      exact ⟨⟨R, comm, dom, dvr, complete, cz, b, hb⟩⟩
    exact hdata)

end CompleteCharZeroDVRLiftData

end AllCharacteristics
