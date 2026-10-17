import PfaffianDescent.FieldTensorInjectiveDimension
import PfaffianDescent.SelfInjectiveDimensionTransport
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

namespace PfaffianDescent
open CategoryTheory TensorProduct MvPolynomial
universe u
section
variable {K L : Type u} {σ : Type} [Field K] [Field L] [Algebra K L]

/-- Base change of a polynomial quotient is the quotient by the extended ideal. -/
noncomputable def polynomialQuotientTensorEquiv (I : Ideal (MvPolynomial σ K)) :
    (MvPolynomial σ K ⧸ I) ⊗[K] L ≃+*
      (MvPolynomial σ L ⧸ I.map (MvPolynomial.map (algebraMap K L))) := by
  let E := MvPolynomial.algebraTensorAlgEquiv (σ := σ) K L
  let j : MvPolynomial σ K →+* L ⊗[K] MvPolynomial σ K :=
    (Algebra.TensorProduct.includeRight : MvPolynomial σ K →ₐ[K] L ⊗[K] MvPolynomial σ K).toRingHom
  have hj : E.toRingHom.comp j = MvPolynomial.map (algebraMap K L) := by
    apply RingHom.ext
    intro p
    change E ((1 : L) ⊗ₜ[K] p) = MvPolynomial.map (algebraMap K L) p
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  have hI : I.map (MvPolynomial.map (algebraMap K L)) = (I.map j).map E.toRingHom := by
    rw [Ideal.map_map, hj]
  exact (Algebra.TensorProduct.comm K (MvPolynomial σ K ⧸ I) L).toRingEquiv.trans
    ((Algebra.TensorProduct.tensorQuotientEquiv (R := K) L (MvPolynomial σ K) L I).toRingEquiv.trans
      (Ideal.quotientEquiv (I.map j) (I.map (MvPolynomial.map (algebraMap K L))) E.toRingEquiv hI))

/-- The finite self-injective-dimension criterion for a polynomial quotient
descends from every extension of its coefficient field. -/
theorem polynomial_quotient_self_injectiveDimensionLE_descent
    (I : Ideal (MvPolynomial σ K)) (n : ℕ)
    [HasInjectiveDimensionLE
      (ModuleCat.of (MvPolynomial σ L ⧸ I.map (MvPolynomial.map (algebraMap K L)))
        (MvPolynomial σ L ⧸ I.map (MvPolynomial.map (algebraMap K L)))) n] :
    HasInjectiveDimensionLE (ModuleCat.of (MvPolynomial σ K ⧸ I) (MvPolynomial σ K ⧸ I)) n := by
  letI : HasInjectiveDimensionLE
      (ModuleCat.of ((MvPolynomial σ K ⧸ I) ⊗[K] L) ((MvPolynomial σ K ⧸ I) ⊗[K] L)) n :=
    (self_injectiveDimensionLE_ringEquiv
      (R := (MvPolynomial σ K ⧸ I) ⊗[K] L)
      (S := MvPolynomial σ L ⧸ I.map (MvPolynomial.map (algebraMap K L)))
      (polynomialQuotientTensorEquiv (L := L) I) n).mpr
    (inferInstance : HasInjectiveDimensionLE
      (ModuleCat.of (MvPolynomial σ L ⧸ I.map (MvPolynomial.map (algebraMap K L)))
        (MvPolynomial σ L ⧸ I.map (MvPolynomial.map (algebraMap K L)))) n)
  exact field_tensor_self_injectiveDimensionLE (K := K) (L := L) n

end
end PfaffianDescent
