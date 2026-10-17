import AllCharacteristics.SchemeSpecialization
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Filtration
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Regular local rings of dimension at most one

The regular-local specialization argument starts with fields and discrete
valuation rings. Here those cases are derived from Mathlib's numerical
definition of regularity. In particular, the domain property in dimension one
is proved rather than included among the hypotheses.
-/

namespace AllCharacteristics
open IsLocalRing

section PrincipalMaximalIdeal
variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- In a Noetherian local ring with principal maximal ideal, every nonzero
element is a power of its generator times a unit. This includes rings with
nilpotents; the proof uses Krull's intersection theorem. -/
theorem exists_pow_mul_unit_of_principal_maximalIdeal (t : R)
    (ht : maximalIdeal R = Ideal.span {t}) (x : R) (hx : x ≠ 0) :
    ∃ (n : ℕ) (u : R), IsUnit u ∧ x = t ^ n * u := by
  classical
  have hav : ∃ n : ℕ, x ∉ maximalIdeal R ^ (n + 1) := by
    by_contra hn
    push Not at hn
    have hm : x ∈ ⨅ n : ℕ, maximalIdeal R ^ n := by
      rw [Submodule.mem_iInf]
      intro n
      cases n with
      | zero => simp
      | succ n => exact hn n
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top] at hm
    exact hx hm
  let n := Nat.find hav
  have hn : x ∉ maximalIdeal R ^ (n + 1) := Nat.find_spec hav
  have hm : x ∈ maximalIdeal R ^ n := by
    by_cases hzero : n = 0
    · simp [hzero]
    · obtain ⟨m, hme⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hmin := Nat.find_min hav (show m < Nat.find hav by change m < n; omega)
      simpa only [hme] using not_not.mp hmin
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
  obtain ⟨u, hu⟩ := hm
  refine ⟨n, u, ?_, hu⟩
  by_contra hnu
  have hu_mem : u ∈ maximalIdeal R := hnu
  rw [ht, Ideal.mem_span_singleton] at hu_mem
  obtain ⟨v, hv⟩ := hu_mem
  apply hn
  rw [ht, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  refine ⟨v, ?_⟩
  rw [hu, hv, pow_succ, mul_assoc]

omit [IsNoetherianRing R] in
/-- A nilpotent generator of the maximal ideal forces dimension zero. -/
theorem krullDim_eq_zero_of_nilpotent_maximal_generator (t : R)
    (ht : maximalIdeal R = Ideal.span {t}) (hn : IsNilpotent t) :
    ringKrullDim R = 0 := by
  have hiff : ∀ x : R, IsNilpotent x ↔ ¬ IsUnit x := by
    intro x
    refine ⟨fun h => h.not_isUnit, ?_⟩
    intro hx
    have hm : x ∈ maximalIdeal R := hx
    rw [ht, Ideal.mem_span_singleton] at hm
    obtain ⟨y, rfl⟩ := hm
    obtain ⟨n, hn⟩ := hn
    exact ⟨n, by rw [mul_pow, hn, zero_mul]⟩
  have hpair : Ring.KrullDimLE 0 R ∧ IsLocalRing R :=
    ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 2 0).mp hiff
  have hz : Ring.KrullDimLE 0 R := hpair.1
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hz

/-- A Noetherian local ring with principal maximal ideal and positive dimension
is a domain. No reducedness assumption is needed. -/
theorem isDomain_of_principal_maximalIdeal_of_dim_ne_zero
    (hm : (maximalIdeal R).IsPrincipal) (hd : ringKrullDim R ≠ 0) : IsDomain R := by
  obtain ⟨t, ht⟩ := hm
  have hn : ¬ IsNilpotent t := fun hn =>
    hd (krullDim_eq_zero_of_nilpotent_maximal_generator t ht hn)
  have : NoZeroDivisors R := by
    constructor
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    by_cases hb : b = 0
    · exact Or.inr hb
    obtain ⟨n, u, hu, hpa⟩ := exists_pow_mul_unit_of_principal_maximalIdeal t ht a ha
    obtain ⟨m, v, hv, hpb⟩ := exists_pow_mul_unit_of_principal_maximalIdeal t ht b hb
    have hprod : t ^ (n + m) * (u * v) = 0 := by
      rw [pow_add, mul_mul_mul_comm, ← hpa, ← hpb]
      exact hab
    exact (hn ⟨n + m, (hu.mul hv).mul_left_eq_zero.mp hprod⟩).elim
  exact NoZeroDivisors.to_isDomain R

end PrincipalMaximalIdeal

section Regular
variable {R : Type*} [CommRing R] [IsRegularLocalRing R]

/-- A zero-dimensional regular local ring is a field. -/
theorem isField_of_regularLocal_dim_zero (hd : ringKrullDim R = 0) : IsField R := by
  have he : (maximalIdeal R).spanFinrank = 0 := by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hd
  apply isField_iff_maximalIdeal_eq.mpr
  exact (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp he

/-- The maximal ideal of a one-dimensional regular local ring is principal. -/
theorem maximalIdeal_isPrincipal_of_regularLocal_dim_one (hd : ringKrullDim R = 1) :
    (maximalIdeal R).IsPrincipal := by
  have he : (maximalIdeal R).spanFinrank = 1 := by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hd
  exact ((maximalIdeal R).spanFinrank_eq_one_iff.mp he).1

/-- A one-dimensional regular local ring is a domain. -/
theorem isDomain_of_regularLocal_dim_one (hd : ringKrullDim R = 1) : IsDomain R :=
  isDomain_of_principal_maximalIdeal_of_dim_ne_zero
    (maximalIdeal_isPrincipal_of_regularLocal_dim_one hd) (by rw [hd]; exact one_ne_zero)

/-- A one-dimensional regular local domain has the valuation-ring property. -/
theorem valuationRing_of_regularLocal_dim_one [IsDomain R] (hd : ringKrullDim R = 1) :
    ValuationRing R :=
  ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 4 1).mp
    (maximalIdeal_isPrincipal_of_regularLocal_dim_one hd)

end Regular

open AlgebraicGeometry CategoryTheory
universe u

/-- Proper specialization at a one-dimensional regular local base. Regularity,
not a separately assumed DVR structure, supplies the valuation-ring property. -/
theorem specialize_proper_point_regularLocal_dim_one
    {R K : Type u} [CommRing R] [IsRegularLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hd : ringKrullDim R = 1) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (h : HasPointOver f (algebraMap R K)) :
    HasPointOver f (IsLocalRing.residue R) := by
  have := isDomain_of_regularLocal_dim_one hd
  have := valuationRing_of_regularLocal_dim_one hd
  exact specialize_proper_point_to_residue f h


/-- Proper specialization over a zero-dimensional regular local ring. -/
theorem specialize_proper_point_regularLocal_dim_zero
    {R K : Type u} [CommRing R] [IsRegularLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hd : ringKrullDim R = 0) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (h : HasPointOver f (algebraMap R K)) :
    HasPointOver f (IsLocalRing.residue R) := by
  let := (isField_of_regularLocal_dim_zero hd).toField
  exact specialize_proper_point_to_residue f h

/-- The regular-local specialization lemma in dimensions zero and one, with no
separately assumed domain or valuation-ring property. -/
theorem specialize_proper_point_regularLocal_dim_le_one
    {R K : Type u} [CommRing R] [IsRegularLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hd : ringKrullDim R ≤ 1) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f]
    (h : HasPointOver f (algebraMap R K)) :
    HasPointOver f (IsLocalRing.residue R) := by
  have hr := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  have hm : (maximalIdeal R).spanFinrank ≤ 1 := by
    rw [← hr] at hd
    exact_mod_cast hd
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with h₀ | h₁
  · apply specialize_proper_point_regularLocal_dim_zero (f := f) _ h
    rw [← hr, h₀]
    rfl
  · apply specialize_proper_point_regularLocal_dim_one (f := f) _ h
    rw [← hr, h₁]
    rfl

end AllCharacteristics
