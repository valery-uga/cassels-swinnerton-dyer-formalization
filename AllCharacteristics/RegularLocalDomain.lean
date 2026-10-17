import AllCharacteristics.RegularParameters
import AllCharacteristics.PrincipalPrimeDomain
import AllCharacteristics.ParameterAvoidance

/-!
# Regular local rings are domains

We induct on the minimal number of generators of the maximal ideal. Prime
avoidance supplies a parameter outside every minimal prime, its quotient is
regular of smaller dimension, and the principal-prime argument recovers the
domain property of the original ring. This includes finite and imperfect
residue fields and mixed characteristic.
-/

namespace AllCharacteristics
open IsLocalRing
universe u

/-- The induction statement for the domain theorem, with the generator count
recorded as a natural number so that no dimension finiteness assumption is added. -/
theorem isDomain_of_regularLocal_generator_count (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
      (maximalIdeal R).spanFinrank = d → IsDomain R := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro R _ _ hd
    by_cases hd₀ : d = 0
    · have hr₀ : ringKrullDim R = 0 := by
        rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, hd, hd₀]
        rfl
      let := (isField_of_regularLocal_dim_zero hr₀).toField
      infer_instance
    have hr : ringKrullDim R ≠ 0 := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, hd]
      exact_mod_cast hd₀
    obtain ⟨x, hx, hx₂, havoid⟩ := exists_parameter_avoiding_minimal_primes hr
    have := isRegularLocalRing_quotient_parameter x hx hx₂
    have hlt : (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank < d := by
      have hb := parameter_quotient_embedding_dimension_bound x hx hx₂
      rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at hb
      omega
    have hdom : IsDomain (R ⧸ Ideal.span {x}) :=
      ih (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank hlt (R ⧸ Ideal.span {x}) rfl
    have : (Ideal.span {x}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdom
    apply isDomain_of_nonminimal_principal_prime x
    intro hmin
    exact havoid (Ideal.span {x}) hmin (Ideal.subset_span rfl)

/-- Every Noetherian regular local ring is an integral domain, using Mathlib's
numerical definition of regularity. -/
theorem isDomain_of_regularLocalRing (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R :=
  isDomain_of_regularLocal_generator_count (maximalIdeal R).spanFinrank R rfl

/-- Every minimal parameter generates a prime ideal, since its quotient is a
regular local ring and hence a domain. -/
theorem isPrime_span_parameter {R : Type u} [CommRing R] [IsRegularLocalRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hx₂ : x ∉ maximalIdeal R ^ 2) :
    (Ideal.span {x}).IsPrime := by
  have := isRegularLocalRing_quotient_parameter x hx hx₂
  have := isDomain_of_regularLocalRing (R ⧸ Ideal.span {x})
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this

end AllCharacteristics
