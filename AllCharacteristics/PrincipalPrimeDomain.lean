import AllCharacteristics.RegularLocalLowDimension

/-!
# A principal prime and the domain property

For the induction on regular local dimension, a suitable parameter has a prime
principal ideal that is not minimal. This file shows that such a parameter
forces the original local ring to be a domain. Krull intersection is used before
localization, so injectivity of localization is proved rather than assumed.
-/

namespace AllCharacteristics
open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Separate the maximal possible power of a nonunit from any nonzero element
in a Noetherian local ring. The remaining factor is outside its principal ideal. -/
theorem exists_pow_mul_not_mem_principal (t : R) (ht : Ideal.span {t} ≠ ⊤)
    (a : R) (ha : a ≠ 0) :
    ∃ (n : ℕ) (u : R), u ∉ Ideal.span {t} ∧ a = t ^ n * u := by
  classical
  let p := Ideal.span {t}
  have hav : ∃ n : ℕ, a ∉ p ^ (n + 1) := by
    by_contra hn
    push Not at hn
    have hm : a ∈ ⨅ n : ℕ, p ^ n := by
      rw [Submodule.mem_iInf]
      intro n
      cases n with
      | zero => simp
      | succ n => exact hn n
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ ht] at hm
    exact ha hm
  let n := Nat.find hav
  have hn : a ∉ p ^ (n + 1) := Nat.find_spec hav
  have hm : a ∈ p ^ n := by
    by_cases hzero : n = 0
    · simp [hzero]
    · obtain ⟨m, hme⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hmin := Nat.find_min hav (show m < Nat.find hav by change m < n; omega)
      simpa only [hme] using not_not.mp hmin
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
  obtain ⟨u, hu⟩ := hm
  refine ⟨n, u, ?_, hu⟩
  intro hum
  rw [Ideal.mem_span_singleton] at hum
  obtain ⟨v, hv⟩ := hum
  apply hn
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨v, by rw [hu, hv, pow_succ, mul_assoc]⟩

/-- A nonminimal principal prime in a Noetherian local ring forces that ring
to be a domain. Neither reducedness nor injectivity of localization is assumed. -/
theorem isDomain_of_nonminimal_principal_prime (t : R)
    [hp : (Ideal.span {t}).IsPrime]
    (hn : Ideal.span {t} ∉ minimalPrimes R) : IsDomain R := by
  let p := Ideal.span {t}
  let S := Localization.AtPrime p
  have hdim : ringKrullDim S ≠ 0 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S]
    intro h
    apply hn
    apply Ideal.height_eq_zero_iff.mp
    exact_mod_cast h
  have hmax : maximalIdeal S = Ideal.span {algebraMap R S t} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_span _ _ |>.trans (by rw [Set.image_singleton])
  have hm : (maximalIdeal S).IsPrincipal := by
    rw [hmax]
    infer_instance
  have : IsDomain S := isDomain_of_principal_maximalIdeal_of_dim_ne_zero hm hdim
  have htS : algebraMap R S t ≠ 0 := by
    intro htS
    have hm0 : maximalIdeal S = ⊥ := by rw [hmax, htS, Ideal.span_singleton_zero]
    exact hdim (ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hm0))
  have hinj : Function.Injective (algebraMap R S) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra han
    obtain ⟨n, u, hu, he⟩ := exists_pow_mul_not_mem_principal t hp.ne_top a han
    have huS : IsUnit (algebraMap R S u) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff S p u).mpr hu
    rw [he, map_mul, map_pow] at ha
    exact (mul_ne_zero (pow_ne_zero n htS) huS.ne_zero) ha
  exact hinj.isDomain (algebraMap R S)

end AllCharacteristics
