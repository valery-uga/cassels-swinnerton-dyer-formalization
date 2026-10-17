import PfaffianDescent.CorayStabilizerOrbitDegree
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-! Literal coefficient orbits are precisely the minimal primes over the
literal extension of an original prime. Projective geometric component
identification and algebraic-closure splitting are separate obligations. -/
noncomputable section
namespace PfaffianDescent.Coray
open scoped Pointwise
universe u
variable {K E : Type u} [Field K] [Field E] [Algebra K E]
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] polynomialGaloisCoefficientAction

/-- Actual orbit equality, deriving both stability and transitivity for the
literal extended original prime; no orbit/component certificate is supplied. -/
theorem polynomialCoefficientExtension_minimalPrimes_eq_orbit
    [FiniteDimensional K E] [IsGalois K E]
    (I : Ideal (MvPolynomial (Fin 4) K)) [I.IsPrime]
    (P : Ideal (MvPolynomial (Fin 4) E))
    (hP : P ∈ (I.map (MvPolynomial.map (algebraMap K E))).minimalPrimes) :
    MulAction.orbit (E ≃ₐ[K] E) P =
      (I.map (MvPolynomial.map (algebraMap K E))).minimalPrimes := by
  classical
  ext Q
  constructor
  · rintro ⟨g, rfl⟩
    change P.map (MvPolynomial.map g.toRingHom) ∈ _
    let f : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) E :=
      MvPolynomial.map (algebraMap K E)
    let j : MvPolynomial (Fin 4) E →+* MvPolynomial (Fin 4) E :=
      MvPolynomial.map g.toRingHom
    have hcomp : j.comp f = f := by
      apply RingHom.ext
      intro q
      apply MvPolynomial.ext
      intro d
      dsimp only [j, f]
      simp only [RingHom.comp_apply, MvPolynomial.coeff_map]
      exact g.commutes (MvPolynomial.coeff d q)
    have hJ : (I.map f).map j = I.map f := by
      rw [Ideal.map_map, hcomp]
    have hsurj : Function.Surjective j :=
      MvPolynomial.map_surjective g.toRingHom g.surjective
    have hinj : Function.Injective j :=
      MvPolynomial.map_injective g.toRingHom g.injective
    have hker : RingHom.ker j = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot j).mp hinj
    have hmin := Ideal.minimalPrimes_map_of_surjective hsurj (I.map f)
    rw [hJ, hker, sup_bot_eq] at hmin
    change P.map j ∈ (I.map f).minimalPrimes
    rw [hmin]
    exact ⟨P, hP, rfl⟩
  · intro hQ
    obtain ⟨g, hg⟩ := polynomialCoefficientExtension_minimalPrimes_conjugate I P Q hP hQ
    exact ⟨g, hg.symm⟩

/-- The actual stabilizer fixed field degree equals the actual number of
minimal primes over the extended original prime. This count is derived. -/
theorem homogeneousMinimalPrime_stabilizerFixedField_finrank_eq_minimalPrimes_card
    [FiniteDimensional K E] [IsGalois K E]
    (I : Ideal (MvPolynomial (Fin 4) K)) [I.IsPrime]
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) E))
    (hC : C.toIdeal ∈ (I.map (MvPolynomial.map (algebraMap K E))).minimalPrimes) :
    Module.finrank K (homogeneousIdealStabilizerFixedField (K := K) C) =
      Nat.card ((I.map (MvPolynomial.map (algebraMap K E))).minimalPrimes) := by
  have h := homogeneousIdeal_stabilizerFixedField_finrank_eq_orbit_card (K := K) C
  rw [polynomialCoefficientExtension_minimalPrimes_eq_orbit I C.toIdeal hC] at h
  exact h

end PfaffianDescent.Coray
