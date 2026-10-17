import AllCharacteristics.RegularParameters
import PfaffianDescent.CorayFullJetDifferentials
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Source only. A nonzero actual native first jet makes the SAME equation
a regular parameter. This algebraic cut does not assert any polynomial,
chart-to-stalk or curve-kernel identification absent from its hypotheses. -/
noncomputable section
namespace PfaffianDescent.Coray
open TrivSqZeroExt
universe u

/-- The kernel of the residue projection of the first-jet ring squares to zero. -/
private theorem firstJet_residueKernel_square_zero001
    {M : Type u} [Field M] :
    (RingHom.ker (TrivSqZeroExt.fstHom M M (Fin 2 → M)).toRingHom) ^ 2 = ⊥ := by
  let J := RingHom.ker (TrivSqZeroExt.fstHom M M (Fin 2 → M)).toRingHom
  change J ^ 2 = ⊥
  apply le_antisymm _ bot_le
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro r hr s hs
  change r.fst = 0 at hr
  change s.fst = 0 at hs
  rw [Ideal.mem_bot]
  apply TrivSqZeroExt.ext
  · simp only [TrivSqZeroExt.fst_mul, hr, hs, zero_mul, TrivSqZeroExt.fst_zero]
  · simp [TrivSqZeroExt.snd_mul, hr, hs]

/-- A local native jet map kills the square of the source maximal ideal. -/
private theorem firstJet_localMap_maximalIdeal_square_zero001
    {R M : Type u} [CommRing R] [IsLocalRing R] [Field M]
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) [IsLocalHom φ] :
    (IsLocalRing.maximalIdeal R ^ 2).map φ = ⊥ := by
  let J := RingHom.ker (TrivSqZeroExt.fstHom M M (Fin 2 → M)).toRingHom
  have hMap : (IsLocalRing.maximalIdeal R).map φ ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change (φ r).fst = 0
    by_contra h
    have hu : IsUnit (φ r) := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
      (isUnit_iff_ne_zero.mpr h)
    have hrunit : IsUnit r := isUnit_of_map_unit φ r hu
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr
    exact hr hrunit
  apply le_antisymm _ bot_le
  rw [Ideal.map_pow]
  calc
    _ ≤ J ^ 2 := by
      simpa only [pow_two] using Ideal.mul_mono hMap hMap
    _ = ⊥ := firstJet_residueKernel_square_zero001

/-- Actual value zero and nonzero native derivative force the SAME element
to be a parameter; regularity of its quotient is derived. -/
theorem nativeFirstJet_nonzero_derivative_regularParameter001
    {R M : Type u} [CommRing R] [IsRegularLocalRing R] [Field M]
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) [IsLocalHom φ]
    (q : R) (hqvalue : (φ q).fst = 0) (hqjet : (φ q).snd ≠ 0) :
    q ∈ IsLocalRing.maximalIdeal R ∧
      q ∉ IsLocalRing.maximalIdeal R ^ 2 ∧
      IsRegularLocalRing (R ⧸ Ideal.span ({q} : Set R)) := by
  have hq : q ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have h := TrivSqZeroExt.isUnit_iff_isUnit_fst.mp (φ.isUnit_map hu)
    exact h.ne_zero hqvalue
  have hqSquare : q ∉ IsLocalRing.maximalIdeal R ^ 2 := by
    intro h
    have hφq : φ q = 0 := by
      apply Ideal.mem_bot.mp
      rw [← firstJet_localMap_maximalIdeal_square_zero001 φ]
      exact Ideal.mem_map_of_mem φ h
    exact hqjet (congrArg TrivSqZeroExt.snd hφq)
  exact ⟨hq, hqSquare,
    AllCharacteristics.isRegularLocalRing_quotient_parameter q hq hqSquare⟩

/-- The actual surjective native curve-stalk map with its SAME principal
kernel transports the derived quotient regularity to its OWN target.
No target regularity is assumed. -/
theorem nativeFirstJet_nonzero_derivative_regular_actualPrincipalTarget001
    {R S M : Type u} [CommRing R] [IsRegularLocalRing R] [CommRing S] [Field M]
    (f : R →+* S) (hf : Function.Surjective f)
    (φ : R →+* TrivSqZeroExt M (Fin 2 → M)) [IsLocalHom φ]
    (q : R) (hKernel : RingHom.ker f = Ideal.span ({q} : Set R))
    (hqvalue : (φ q).fst = 0) (hqjet : (φ q).snd ≠ 0) :
    IsRegularLocalRing S := by
  letI : IsRegularLocalRing (R ⧸ Ideal.span ({q} : Set R)) :=
    (nativeFirstJet_nonzero_derivative_regularParameter001 φ q hqvalue hqjet).2.2
  let e : (R ⧸ Ideal.span ({q} : Set R)) ≃+* S :=
    (Ideal.quotEquivOfEq hKernel.symm).trans (f.quotientKerEquivOfSurjective hf)
  exact IsRegularLocalRing.of_ringEquiv e

end PfaffianDescent.Coray
