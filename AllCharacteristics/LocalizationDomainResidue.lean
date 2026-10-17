import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Residue fields of localizations at kernels

A surjection from a commutative ring onto a domain extends to a surjection
from the localization at its kernel onto the fraction field of that domain.
The construction keeps the original coefficient map exactly.
-/

namespace AllCharacteristics
universe u v
variable {B : Type u} {C : Type v} [CommRing B] [CommRing C] [IsDomain C]

/-- Outside the kernel, reduction to the fraction field gives units. -/
theorem localizationResidueMap_units (b : B →+* C) (J : Ideal B) [J.IsPrime]
    (hJ : J = RingHom.ker b) (s : J.primeCompl) :
    IsUnit (((algebraMap C (FractionRing C)).comp b) s) := by
  apply IsUnit.mk0
  intro h
  have he : b s = 0 := (FaithfulSMul.algebraMap_injective C (FractionRing C))
    (h.trans (map_zero (algebraMap C (FractionRing C))).symm)
  exact s.property (by simpa only [hJ, SetLike.mem_coe, RingHom.mem_ker] using he)

/-- The residue map from the localization at the kernel to the fraction
field of the quotient domain. -/
noncomputable def localizationResidueMap (b : B →+* C) (J : Ideal B) [J.IsPrime]
    (hJ : J = RingHom.ker b) : Localization.AtPrime J →+* FractionRing C :=
  IsLocalization.lift (localizationResidueMap_units b J hJ)

/-- The localized map agrees with reduction on all original elements. -/
theorem localizationResidueMap_algebraMap (b : B →+* C) (J : Ideal B) [J.IsPrime]
    (hJ : J = RingHom.ker b) (x : B) :
    localizationResidueMap b J hJ (algebraMap B (Localization.AtPrime J) x) =
      algebraMap C (FractionRing C) (b x) :=
  IsLocalization.lift_eq (localizationResidueMap_units b J hJ) x

/-- Surjectivity onto the quotient domain gives surjectivity of the
localized residue map onto its full fraction field. -/
theorem localizationResidueMap_surjective (b : B →+* C) (hb : Function.Surjective b)
    (J : Ideal B) [J.IsPrime] (hJ : J = RingHom.ker b) :
    Function.Surjective (localizationResidueMap b J hJ) := by
  intro y
  obtain ⟨a, c, hc, rfl⟩ := IsFractionRing.div_surjective C y
  obtain ⟨p, hp⟩ := hb a
  obtain ⟨q, hq⟩ := hb c
  have hqn : q ∉ J := by
    intro h
    have hzero : b q = 0 := by simpa only [hJ, RingHom.mem_ker] using h
    exact (nonZeroDivisors.ne_zero hc) (hq.symm.trans hzero)
  refine ⟨IsLocalization.mk' (Localization.AtPrime J) p (⟨q, hqn⟩ : J.primeCompl), ?_⟩
  apply (IsLocalization.lift_mk'_spec (localizationResidueMap_units b J hJ)
    p _ (⟨q, hqn⟩ : J.primeCompl)).mpr
  change algebraMap C (FractionRing C) (b p) =
    algebraMap C (FractionRing C) (b q) *
      (algebraMap C (FractionRing C) a / algebraMap C (FractionRing C) c)
  rw [hp, hq, mul_comm, div_mul_cancel₀ _
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hc)]

end AllCharacteristics
