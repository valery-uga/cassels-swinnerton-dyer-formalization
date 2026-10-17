import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

noncomputable section
namespace PfaffianDescent
open scoped TensorProduct
universe u v w
variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
variable {σ : Type w} (I : Ideal (MvPolynomial σ R))

/-- Scalar extension of the entire polynomial quotient, with no flatness premise. -/
def polynomialWholeIdealScalarExtension286 :
    S ⊗[R] (MvPolynomial σ R ⧸ I) ≃ₐ[S]
      MvPolynomial σ S ⧸ I.map (MvPolynomial.map (algebraMap R S)) := by
  let e : S ⊗[R] MvPolynomial σ R ≃ₐ[S] MvPolynomial σ S :=
    MvPolynomial.algebraTensorAlgEquiv R S
  have hc : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := MvPolynomial σ R)).toRingHom =
      MvPolynomial.map (algebraMap R S) := by
    apply RingHom.ext
    intro p
    change e (1 ⊗ₜ[R] p) = MvPolynomial.map (algebraMap R S) p
    exact (MvPolynomial.algebraTensorAlgEquiv_tmul R S 1 p).trans (one_smul S _)
  have hi : I.map (MvPolynomial.map (algebraMap R S)) =
      (I.map (Algebra.TensorProduct.includeRight (R := R) (A := S)
        (B := MvPolynomial σ R)).toRingHom).map e.toRingHom := by
    rw [Ideal.map_map, hc]
  exact (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (MvPolynomial σ R) S I).trans
    (Ideal.quotientEquivAlg _ _ e hi)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma polynomialWholeIdealScalarExtension_tmul286 (s : S) (p : MvPolynomial σ R) :
    polynomialWholeIdealScalarExtension286 S I (s ⊗ₜ[R] Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap R S)))
        (s • MvPolynomial.map (algebraMap R S) p) := by
  rw [polynomialWholeIdealScalarExtension286, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul, Ideal.quotientEquivAlg_mk,
    MvPolynomial.algebraTensorAlgEquiv_tmul]

end PfaffianDescent
