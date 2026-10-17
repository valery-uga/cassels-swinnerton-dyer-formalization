import AllCharacteristics.RegularLocalDomain
import AllCharacteristics.RelativeSpecialization

/-!
# Proper specialization over a regular local ring

This is the full regular-local specialization lemma of Section 3 of
`all_characteristics_specialization.tex`, with no dimension bound. The induction
uses actual ring quotients, prime localizations, their residue fields, and the
valuative criterion for actual proper schemes. The original ambient base map is
retained throughout the induction.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
open IsLocalRing
universe u

/-- The induction statement permits any surjective residue map and keeps the
proper scheme over a fixed ambient base, so each parameter quotient can be used
without introducing an assumed specialization principle. -/
theorem specialize_proper_point_regular_generator_count
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [UniversallyClosed f] (d : ℕ) :
    ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R]
      (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
      (k : Type u) [Field k] (red : R →+* k) (_hred : Function.Surjective red)
      (a : A →+* R),
      (maximalIdeal R).spanFinrank = d →
      HasPointOver f ((algebraMap R K).comp a) → HasPointOver f (red.comp a) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro R _ _ K _ _ _ k _ red hred a hd h
    by_cases hd₀ : d = 0
    · have hr₀ : ringKrullDim R = 0 := by
        rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, hd, hd₀]
        rfl
      let := (isField_of_regularLocal_dim_zero hr₀).toField
      exact specialize_proper_point_along_valuation f a red h
    have hr : ringKrullDim R ≠ 0 := by
      rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, hd]
      exact_mod_cast hd₀
    have := isDomain_of_regularLocalRing R
    obtain ⟨x, hx, hx₂, _⟩ := exists_parameter_avoiding_minimal_primes hr
    have := isPrime_span_parameter x hx hx₂
    let p := Ideal.span {x}
    let Q := R ⧸ p
    let V := Localization.AtPrime p
    have : IsRegularLocalRing Q := isRegularLocalRing_quotient_parameter x hx hx₂
    have hm : (maximalIdeal V).IsPrincipal := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      change (p.map (algebraMap R V)).IsPrincipal
      rw [Ideal.map_span, Set.image_singleton]
      infer_instance
    have : ValuationRing V :=
      ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain V).out 4 1).mp hm
    have hc := HasPointOver.canonicalFractionRing a h
    have hvg : HasPointOver f ((algebraMap V (FractionRing R)).comp
        ((algebraMap R V).comp a)) := by
      rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R V (FractionRing R)]
      exact hc
    have hE : HasPointOver f ((algebraMap Q p.ResidueField).comp
        ((Ideal.Quotient.mk p).comp a)) := by
      have hh := specialize_proper_point_along_valuation f ((algebraMap R V).comp a)
        (IsLocalRing.residue V) hvg
      exact hh
    have : IsLocalHom red := IsLocalHom.of_surjective red hred
    have hxred : red x = 0 := by
      have hh := map_nonunit red x hx
      rw [maximalIdeal_eq_bot, Submodule.mem_bot] at hh
      exact hh
    have hpker : p ≤ RingHom.ker red := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hxred
    let redQ : Q →+* k := Ideal.Quotient.lift p red (fun r hr => hpker hr)
    have hredQ : Function.Surjective redQ :=
      Ideal.Quotient.lift_surjective_of_surjective p _ hred
    have hlt : (maximalIdeal Q).spanFinrank < d := by
      have hb := parameter_quotient_embedding_dimension_bound x hx hx₂
      rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at hb
      change (maximalIdeal Q).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank at hb
      omega
    have hout := ih (maximalIdeal Q).spanFinrank hlt Q p.ResidueField k redQ hredQ
      ((Ideal.Quotient.mk p).comp a) rfl hE
    exact hout

/-- A generic point of a proper scheme over a regular local ring specializes to
its residue field. This is the addendum's regular-local specialization lemma in
arbitrary dimension and arbitrary characteristic. -/
theorem specialize_proper_point_regularLocal
    {R K : Type u} [CommRing R] [IsRegularLocalRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (h : HasPointOver f (algebraMap R K)) :
    HasPointOver f (IsLocalRing.residue R) := by
  exact specialize_proper_point_regular_generator_count f (maximalIdeal R).spanFinrank
    R K (ResidueField R) (IsLocalRing.residue R) residue_surjective (RingHom.id R) rfl h

end AllCharacteristics
