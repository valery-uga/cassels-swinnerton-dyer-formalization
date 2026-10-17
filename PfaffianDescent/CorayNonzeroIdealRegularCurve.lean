import AllCharacteristics.RegularLocalLowDimension
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Maps
import PfaffianDescent.VoisinFixedCurveStalkwiseCartierCriterion

/-! SOURCE ONLY / UNCOMPILED156. Entire nonzero ideals, including powers and
nonradical ideals, on regular domains of dimension at most one. -/
noncomputable section
namespace PfaffianDescent.Coray
open IsLocalRing
universe u

/-- Every regular local domain of dimension at most one is a PID. -/
theorem regularLocalDomain_isPrincipalIdealRing_of_dimension_le_one
    {A : Type u} [CommRing A] [IsRegularLocalRing A] [IsDomain A]
    (hdim : ringKrullDim A ≤ 1) : IsPrincipalIdealRing A := by
  have hrank : (maximalIdeal A).spanFinrank ≤ 1 := by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)).trans_le hdim
  have hmprincipal : (maximalIdeal A).IsPrincipal := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hrank with hzero | hone
    · have hmzero : maximalIdeal A = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot
          (IsNoetherian.noetherian (maximalIdeal A))).mp hzero
      rw [hmzero]
      infer_instance
    · exact ((maximalIdeal A).spanFinrank_eq_one_iff.mp hone).1
  exact ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain A).out 4 0).mp hmprincipal

/-- Principal generation and regularity apply to the ENTIRE nonzero ideal;
no primality or radical condition on the ideal is used. -/
theorem regularLocalDomain_nonzeroIdeal_regularPrincipal
    {A : Type u} [CommRing A] [IsRegularLocalRing A] [IsDomain A]
    (hdim : ringKrullDim A ≤ 1) (I : Ideal A) (hI : I ≠ ⊥) :
    ∃ z : A, IsRegular z ∧ I = Ideal.span ({z} : Set A) := by
  letI : IsPrincipalIdealRing A :=
    regularLocalDomain_isPrincipalIdealRing_of_dimension_le_one hdim
  obtain ⟨z, hz⟩ := IsPrincipalIdealRing.principal I
  have hz0 : z ≠ 0 := by
    intro hzero
    apply hI
    simpa only [hzero, Ideal.span_singleton_zero] using hz
  exact ⟨z, isRegular_iff_ne_zero.mpr hz0, hz⟩

/-- Localization preserves nonzero of the entire ideal and makes it regular
principal. This includes stalks outside its support, where it is the unit ideal. -/
theorem regularDomain_nonzeroIdeal_atPrime_regularPrincipal
    {A : Type u} [CommRing A] [IsRegularRing A] [IsDomain A]
    (hdim : ringKrullDim A ≤ 1) (I : Ideal A) (hI : I ≠ ⊥)
    (Q : Ideal A) [Q.IsPrime] :
    ∃ z : Localization.AtPrime Q, IsRegular z ∧
      I.map (algebraMap A (Localization.AtPrime Q)) =
        Ideal.span ({z} : Set (Localization.AtPrime Q)) := by
  have hlocDim : ringKrullDim (Localization.AtPrime Q) ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)]
    exact (Ideal.height_le_ringKrullDim_of_ne_top
      (Ideal.IsPrime.ne_top' (I := Q))).trans hdim
  have hinj : Function.Injective (algebraMap A (Localization.AtPrime Q)) :=
    IsLocalization.injective (Localization.AtPrime Q) Q.primeCompl_le_nonZeroDivisors
  have hlocNe : I.map (algebraMap A (Localization.AtPrime Q)) ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective hinj).mp.mt hI
  exact regularLocalDomain_nonzeroIdeal_regularPrincipal hlocDim _ hlocNe

/-- Finite generation and denominator clearing spread each entire ideal's
local generator to a basic open containing the original prime. -/
theorem regularDomain_nonzeroIdeal_basicOpen_regularPrincipal
    {A : Type u} [CommRing A] [IsRegularRing A] [IsDomain A]
    (hdim : ringKrullDim A ≤ 1) (I : Ideal A) (hI : I ≠ ⊥)
    (Q : Ideal A) [Q.IsPrime] :
    ∃ s : A, s ∉ Q ∧ ∃ z : A, z ∈ I ∧
      IsRegular (algebraMap A (Localization.Away s) z) ∧
      I.map (algebraMap A (Localization.Away s)) =
        Ideal.span ({algebraMap A (Localization.Away s) z} :
          Set (Localization.Away s)) :=
  PfaffianDescent.ideal_localRegularPrincipal_spreads_to_basicOpen I Q
    (Ideal.fg_of_isNoetherianRing I)
    (regularDomain_nonzeroIdeal_atPrime_regularPrincipal hdim I hI Q)

end PfaffianDescent.Coray
