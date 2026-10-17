import PfaffianDescent.CubicPolynomialJetMinorTransport

/-! Opaque field-level equation proofs keep native configuration-field
factories from repeatedly expanding their fraction-ring instances. -/

noncomputable section
namespace PfaffianDescent

open MvPolynomial
universe u

theorem cubicFullJetCoordinates_residue
    {E : Type u} [Field E] (x : Fin 11 → Fin 4 → E)
    (rows : Fin 3 → Fin 4 → Fin 2 → E) (k : Fin 3) (r : Fin 4) :
    (cubicFullJetCoordinates x rows k r).fst = x (k.castAdd 8) r := by
  simp only [cubicFullJetCoordinates, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]

theorem cubicPolynomialSurfaceTangentRows_firstJets_cubic_of_eval
    {E : Type u} [Field E]
    (p : MvPolynomial (Fin 4) E) (x : Fin 11 → Fin 4 → E)
    (anchor : Fin 3 → Fin 4) (pivot : Fin 3 → Fin 3)
    (hpx : ∀ k, p.eval (x k) = 0) :
    ∀ k, aeval (cubicFullJetCoordinates x
      (cubicPolynomialSurfaceTangentRows p x anchor pivot) k) p = 0 := by
  exact cubicPolynomialSurfaceTangentRows_firstJets_cubic p x anchor pivot
    (fun k => by simpa only [aeval_eq_eval] using hpx (k.castAdd 8))

end PfaffianDescent
