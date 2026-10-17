import AllCharacteristics.RegularLocalLowDimension
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Separated local rings with principal maximal ideal

Adic separatedness replaces the noetherian hypothesis in the uniformizer
factorization argument. With a nonnilpotent generator, the ring is a domain
and then a discrete valuation ring. This applies to a DVR completion without
first assuming noetherianness or reducedness of that completion.
-/

open IsLocalRing
namespace AllCharacteristics
universe u
variable {A : Type u} [CommRing A] [IsLocalRing A]
  [IsHausdorff (maximalIdeal A) A]

/-- Separatedness and a principal maximal ideal factor each nonzero element
as a power of the maximal-ideal generator times a unit. -/
theorem exists_pow_mul_unit_of_separated_principal_maximalIdeal
    (t : A) (ht : maximalIdeal A = Ideal.span {t}) (x : A) (hx : x ≠ 0) :
    ∃ (n : ℕ) (v : A), IsUnit v ∧ x = t ^ n * v := by
  classical
  have hav : ∃ n : ℕ, x ∉ maximalIdeal A ^ (n + 1) := by
    by_contra hn
    push Not at hn
    apply hx
    apply IsHausdorff.haus (I := maximalIdeal A) inferInstance x
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    cases n with
    | zero => simp
    | succ n => exact hn n
  let n := Nat.find hav
  have hn : x ∉ maximalIdeal A ^ (n + 1) := Nat.find_spec hav
  have hm : x ∈ maximalIdeal A ^ n := by
    by_cases hzero : n = 0
    · simp [hzero]
    · obtain ⟨m, hme⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hmin := Nat.find_min hav (show m < Nat.find hav by change m < n; omega)
      simpa only [hme] using not_not.mp hmin
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
  obtain ⟨v, hv⟩ := hm
  refine ⟨n, v, ?_, hv⟩
  by_contra hnu
  have hm : v ∈ maximalIdeal A := hnu
  rw [ht, Ideal.mem_span_singleton] at hm
  obtain ⟨w, hw⟩ := hm
  apply hn
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨w, ?_⟩
  rw [hv, hw, pow_succ, mul_assoc]

/-- A separated local ring with nonnilpotent principal maximal-ideal
generator is a domain. -/
theorem isDomain_of_separated_principal_maximalIdeal
    (t : A) (ht : maximalIdeal A = Ideal.span {t}) (hn : ¬ IsNilpotent t) : IsDomain A := by
  have : NoZeroDivisors A := by
    constructor
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    by_cases hb : b = 0
    · exact Or.inr hb
    obtain ⟨n, v, hv, hav⟩ := exists_pow_mul_unit_of_separated_principal_maximalIdeal t ht a ha
    obtain ⟨m, w, hw, hbw⟩ := exists_pow_mul_unit_of_separated_principal_maximalIdeal t ht b hb
    have he : t ^ (n + m) * (v * w) = 0 := by
      rw [pow_add, mul_mul_mul_comm, ← hav, ← hbw]
      exact hab
    exact (hn ⟨n + m, (hv.mul hw).mul_left_eq_zero.mp he⟩).elim
  exact NoZeroDivisors.to_isDomain A

/-- A separated local domain with nonzero principal maximal-ideal generator
is a DVR, without a prior noetherian assumption. -/
theorem isDiscreteValuationRing_of_separated_principal_maximalIdeal [IsDomain A]
    (t : A) (ht : maximalIdeal A = Ideal.span {t}) (hne : t ≠ 0) :
    IsDiscreteValuationRing A := by
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨t, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal t hne ht, ?_⟩
  intro x hx
  obtain ⟨n, v, hv, he⟩ := exists_pow_mul_unit_of_separated_principal_maximalIdeal t ht x hx
  obtain ⟨v, rfl⟩ := hv
  exact ⟨n, v, he.symm⟩

end AllCharacteristics
