import PfaffianDescent.WholeQuotientMonomialIdealBaseChange286
import PfaffianDescent.MonomialBasisContainingOne284

noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
universe u v
variable {K : Type u} [Field K] {S : Type v} [CommRing S] {m : ℕ}

/-- An arbitrary nontrivial finite whole polynomial quotient supplies its own
monomial chart and finite generators. Its mapped whole ideal has the native
mapped action kernel and a finite free quotient; no chart/basis/cyclicity
or kernel agreement is supplied by the caller. -/
theorem finiteWholeIdeal_monomialChart_and_baseChange286
    (I : Ideal (MvPolynomial (Fin m) K))
    [Nontrivial (MvPolynomial (Fin m) K ⧸ I)]
    [Module.Finite K (MvPolynomial (Fin m) K ⧸ I)] (f : K →+* S) :
    ∃ (B : Fin (Module.finrank K (MvPolynomial (Fin m) K ⧸ I)) → (Fin m →₀ ℕ))
      (k : Fin (Module.finrank K (MvPolynomial (Fin m) K ⧸ I)))
      (b : Basis (Fin (Module.finrank K (MvPolynomial (Fin m) K ⧸ I))) K
        (MvPolynomial (Fin m) K ⧸ I)),
      B k = 0 ∧ (∀ j, b j = Ideal.Quotient.mk I (monomial (B j) 1)) ∧
      I = cyclicActionGeneratorIdeal285
        (commutingMatrixPolynomialAction282 (wholeQuotientMultiplicationMatrix283 I b)
          (wholeQuotientMultiplicationMatrix_commute283 I b)) B k ∧
      I.map (MvPolynomial.map f) =
        RingHom.ker (wholeQuotientMappedPolynomialAction286 I b f).toRingHom ∧
      Module.Free S (MvPolynomial (Fin m) S ⧸ I.map (MvPolynomial.map f)) ∧
      Module.Finite S (MvPolynomial (Fin m) S ⧸ I.map (MvPolynomial.map f)) := by
  obtain ⟨B, k, b, hk, _, hb⟩ := exists_polynomialImageMonomialBasis_containing_one284
    (Ideal.Quotient.mkₐ K I) (Ideal.Quotient.mkₐ_surjective K I)
  refine ⟨B, k, b, hk, hb, wholeQuotientOriginalIdeal_generators286 I b B k hb hk,
    wholeQuotientMappedPolynomialAction_kernel286 I b f B k hb hk, ?_⟩
  exact wholeQuotientBaseChanged_free_finite286 I b f B k hb hk

end PfaffianDescent
