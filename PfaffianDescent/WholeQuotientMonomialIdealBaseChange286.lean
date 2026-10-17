import PfaffianDescent.WholeQuotientMonomialMatrixIntake283
import PfaffianDescent.CyclicMatrixActionKernelBaseChange285
import PfaffianDescent.PolynomialWholeIdealScalarExtension286

noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
universe u v
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {m n : ℕ}
variable (I : Ideal (MvPolynomial (Fin m) R))
variable (b : Basis (Fin n) R (MvPolynomial (Fin m) R ⧸ I))
variable (f : R →+* S)

def wholeQuotientMappedPolynomialAction286 :
    MvPolynomial (Fin m) S →ₐ[S] Module.End S (Fin n → S) :=
  commutingMatrixPolynomialAction282 (fun i => (wholeQuotientMultiplicationMatrix283 I b i).map f)
    (commutingMatrix_tuple_map_commute285 (wholeQuotientMultiplicationMatrix283 I b)
      (wholeQuotientMultiplicationMatrix_commute283 I b) f)

variable (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
variable (hb : ∀ j, b j = Ideal.Quotient.mk I (monomial (B j) 1)) (hk : B k = 0)

include hb hk in
lemma wholeQuotientMappedPolynomialAction_cyclic286 (j : Fin n) :
    wholeQuotientMappedPolynomialAction286 I b f (monomial (B j) 1) (Pi.single k 1) =
      Pi.single j 1 :=
  commutingMatrixAction_cyclic_map285 (wholeQuotientMultiplicationMatrix283 I b)
    (wholeQuotientMultiplicationMatrix_commute283 I b) f
    (fun i => (wholeQuotientMultiplicationMatrix283 I b i).map f)
    (commutingMatrix_tuple_map_commute285 (wholeQuotientMultiplicationMatrix283 I b)
      (wholeQuotientMultiplicationMatrix_commute283 I b) f) (fun _ => rfl) B k
    (wholeQuotientMultiplicationMatrix_cyclic283 I b B k hb hk) j

include hb hk in
lemma wholeQuotientMappedPolynomialAction_kernel286 :
    I.map (MvPolynomial.map f) =
      RingHom.ker (wholeQuotientMappedPolynomialAction286 I b f).toRingHom := by
  have h := commutingMatrixActionKernel_mapped285 (wholeQuotientMultiplicationMatrix283 I b)
    (wholeQuotientMultiplicationMatrix_commute283 I b) f B k
    (wholeQuotientMultiplicationMatrix_cyclic283 I b B k hb hk)
  rw [wholeQuotientPolynomialAction_ker_eq283 I b] at h
  exact h

include hb hk in
lemma wholeQuotientOriginalIdeal_generators286 :
    I = cyclicActionGeneratorIdeal285
      (commutingMatrixPolynomialAction282 (wholeQuotientMultiplicationMatrix283 I b)
        (wholeQuotientMultiplicationMatrix_commute283 I b)) B k := by
  exact (wholeQuotientPolynomialAction_ker_eq283 I b).symm.trans
    (cyclicActionKernel_eq_generatorIdeal285 _ B k
      (wholeQuotientMultiplicationMatrix_cyclic283 I b B k hb hk))

include hb hk in
lemma wholeQuotientOriginalIdeal_fg286 : I.FG := by
  rw [wholeQuotientOriginalIdeal_generators286 I b B k hb hk]
  exact cyclicActionGeneratorIdeal_fg285 _ B k

include hb hk in
lemma wholeQuotientBaseChanged_free_finite286 :
    Module.Free S (MvPolynomial (Fin m) S ⧸ I.map (MvPolynomial.map f)) ∧
      Module.Finite S (MvPolynomial (Fin m) S ⧸ I.map (MvPolynomial.map f)) := by
  rw [wholeQuotientMappedPolynomialAction_kernel286 I b f B k hb hk]
  exact cyclicPolynomialQuotient_free_finite281 (wholeQuotientMappedPolynomialAction286 I b f)
    (Pi.single k 1) B (wholeQuotientMappedPolynomialAction_cyclic286 I b f B k hb hk)

include hb hk in
lemma wholeQuotientBaseChanged_monomialBasis_exists286 :
    ∃ bS : Basis (Fin n) S (MvPolynomial (Fin m) S ⧸ I.map (MvPolynomial.map f)),
      ∀ j, bS j = Ideal.Quotient.mk (I.map (MvPolynomial.map f)) (monomial (B j) 1) := by
  let h := wholeQuotientMappedPolynomialAction_kernel286 I b f B k hb hk
  let bK := cyclicPolynomialQuotientMonomialBasis281
    (wholeQuotientMappedPolynomialAction286 I b f) (Pi.single k 1) B
    (wholeQuotientMappedPolynomialAction_cyclic286 I b f B k hb hk)
  refine ⟨bK.map (Ideal.quotientEquivAlgOfEq S h.symm).toLinearEquiv, ?_⟩
  intro j
  rw [Basis.map_apply]
  change Ideal.quotientEquivAlgOfEq S h.symm (bK j) = _
  dsimp only [bK]
  rw [cyclicPolynomialQuotientMonomialBasis_apply281, Ideal.quotientEquivAlgOfEq_mk]

end PfaffianDescent
