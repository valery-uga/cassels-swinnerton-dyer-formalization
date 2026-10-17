import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Multiplicity

/-!
# Discrete valuation rings from principal prime localization

A principal prime has a DVR localization if its generator has finite
multiplicity in every nonzero element. No noetherian assumption is required
on the original ring, allowing polynomial rings with arbitrary variable sets.
-/

open IsLocalRing
namespace AllCharacteristics
universe u

/-- Localizing a nonzero principal prime with finite element multiplicities
produces a DVR, even if the original domain is not noetherian. -/
theorem isDiscreteValuationRing_atPrincipalPrime
    {B : Type u} [CommRing B] [IsDomain B]
    (J : Ideal B) [J.IsPrime] (t : B) (ht : t ≠ 0)
    (hJ : J = Ideal.span {t})
    (hfin : ∀ x : B, x ≠ 0 → FiniteMultiplicity t x) :
    IsDiscreteValuationRing (Localization.AtPrime J) := by
  let A := Localization.AtPrime J
  have hi := FaithfulSMul.algebraMap_injective B A
  have hne : algebraMap B A t ≠ 0 := by
    intro h
    exact ht (hi (h.trans (map_zero (algebraMap B A)).symm))
  have hm : maximalIdeal A = Ideal.span {algebraMap B A t} := by
    calc
      maximalIdeal A = J.map (algebraMap B A) :=
        Localization.AtPrime.map_eq_maximalIdeal.symm
      _ = (Ideal.span {t}).map (algebraMap B A) :=
        congrArg (Ideal.map (algebraMap B A)) hJ
      _ = Ideal.span {algebraMap B A t} := by
        rw [Ideal.map_span, Set.image_singleton]
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨algebraMap B A t,
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne hm, ?_⟩
  intro x hx
  obtain ⟨p, s, rfl⟩ := IsLocalization.exists_mk'_eq J.primeCompl x
  have hp : p ≠ 0 := by
    rintro rfl
    exact hx (IsLocalization.mk'_zero s)
  obtain ⟨q, hpq, hq⟩ := (hfin p hp).exists_eq_pow_mul_and_not_dvd
  have hunit : IsUnit (IsLocalization.mk' A q s) := by
    apply (IsLocalization.AtPrime.isUnit_mk'_iff A J q s).mpr
    change q ∉ J
    simpa only [hJ, Ideal.mem_span_singleton] using hq
  obtain ⟨v, hv⟩ := hunit
  refine ⟨multiplicity t p, v, ?_⟩
  rw [hv, ← map_pow, IsLocalization.mul_mk'_eq_mk'_of_mul, ← hpq]

end AllCharacteristics
