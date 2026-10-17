import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Faithfully flat polynomial coefficient extension

For a field extension, extending the coefficients of a multivariate
polynomial ring is faithfully flat.  The explicit tensor--polynomial linear
equivalence below keeps this fact available with the coefficient map written
as `MvPolynomial.map`.
-/

namespace PfaffianDescent

open MvPolynomial TensorProduct
open scoped TensorProduct

universe u v

variable {k K : Type u} {σ : Type v} [Field k] [Field K] [Algebra k K]

attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Tensoring a polynomial ring with its coefficient extension on the left
is linear over the original polynomial ring. -/
noncomputable def tensorPolynomialCoefficientLinearEquiv :
    (K ⊗[k] MvPolynomial σ k) ≃ₗ[MvPolynomial σ k] MvPolynomial σ K := by
  let f : K ⊗[k] MvPolynomial σ k →ₗ[MvPolynomial σ k] MvPolynomial σ K :=
    { toFun := MvPolynomial.algebraTensorAlgEquiv k K
      map_add' := (MvPolynomial.algebraTensorAlgEquiv k K).map_add
      map_smul' := by
        intro p x
        induction x with
        | zero => simp
        | tmul a q =>
          rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
            Algebra.TensorProduct.tmul_mul_tmul]
          simp only [one_mul]
          rw [Algebra.smul_def]
          change (MvPolynomial.algebraTensorAlgEquiv k K) (a ⊗ₜ (p * q)) =
            (MvPolynomial.map (algebraMap k K) p) *
              ((MvPolynomial.algebraTensorAlgEquiv k K) (a ⊗ₜ q))
          simp [MvPolynomial.algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul,
            mul_left_comm]
        | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy }
  exact LinearEquiv.ofBijective f (MvPolynomial.algebraTensorAlgEquiv k K).bijective

/-- Polynomial coefficient extension along a field extension is faithfully
flat. -/
theorem mvPolynomial_coefficientExtension_faithfullyFlat :
    Module.FaithfullyFlat (MvPolynomial σ k) (MvPolynomial σ K) := by
  let P := MvPolynomial σ k
  let e₁ : P ⊗[k] K ≃ₗ[P] K ⊗[k] P :=
    (Algebra.TensorProduct.commRight k P K).toLinearEquiv
  let e := e₁.trans (tensorPolynomialCoefficientLinearEquiv (k := k) (K := K))
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

/-- Extending an ideal along a field coefficient extension and contracting it
back recovers the original ideal. -/
theorem mvPolynomial_comap_map_coefficientExtension
    (I : Ideal (MvPolynomial σ k)) :
    Ideal.comap (MvPolynomial.map (algebraMap k K))
      (I.map (MvPolynomial.map (algebraMap k K))) = I := by
  letI : Module.FaithfullyFlat (MvPolynomial σ k) (MvPolynomial σ K) :=
    mvPolynomial_coefficientExtension_faithfullyFlat
  change Ideal.comap (algebraMap (MvPolynomial σ k) (MvPolynomial σ K))
      (I.map (algebraMap (MvPolynomial σ k) (MvPolynomial σ K))) = I
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

/-- The polynomial-ring part of coefficient extension. -/
noncomputable def polynomialCoefficientTensorRingEquiv :
    K ⊗[k] MvPolynomial σ k ≃ₐ[K] MvPolynomial σ K :=
  MvPolynomial.algebraTensorAlgEquiv k K

theorem polynomialCoefficientTensorIdeal_map
    (I : Ideal (MvPolynomial σ k)) :
    I.map (MvPolynomial.map (algebraMap k K)) =
      (I.map (Algebra.TensorProduct.includeRight (R := k) (A := K)
        (B := MvPolynomial σ k))).map
        (↑(polynomialCoefficientTensorRingEquiv (k := k) (K := K) (σ := σ)) :
          K ⊗[k] MvPolynomial σ k →+* MvPolynomial σ K) := by
  let E := polynomialCoefficientTensorRingEquiv (k := k) (K := K) (σ := σ)
  have hcomp : (↑E : K ⊗[k] MvPolynomial σ k →+* MvPolynomial σ K).comp
      (↑(Algebra.TensorProduct.includeRight (R := k) (A := K)
        (B := MvPolynomial σ k)) : MvPolynomial σ k →+*
          K ⊗[k] MvPolynomial σ k) =
      MvPolynomial.map (algebraMap k K) := by
    apply RingHom.ext
    intro p
    change E (1 ⊗ₜ p) = MvPolynomial.map (algebraMap k K) p
    change (MvPolynomial.algebraTensorAlgEquiv (σ := σ) k K) (1 ⊗ₜ p) =
      MvPolynomial.map (algebraMap k K) p
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  calc
    I.map (MvPolynomial.map (algebraMap k K)) = I.map
        ((↑E : K ⊗[k] MvPolynomial σ k →+* MvPolynomial σ K).comp
          (↑(Algebra.TensorProduct.includeRight (R := k) (A := K)
            (B := MvPolynomial σ k)) : MvPolynomial σ k →+*
              K ⊗[k] MvPolynomial σ k)) :=
      congrArg I.map hcomp.symm
    _ = (I.map (Algebra.TensorProduct.includeRight (R := k) (A := K)
      (B := MvPolynomial σ k))).map
        (↑(polynomialCoefficientTensorRingEquiv (k := k) (K := K) (σ := σ)) :
          K ⊗[k] MvPolynomial σ k →+* MvPolynomial σ K) :=
      (Ideal.map_map _ _).symm

/-- The quotient-ring part of coefficient extension. -/
noncomputable def polynomialCoefficientTensorQuotientAlgEquiv
    (I : Ideal (MvPolynomial σ k)) :
    ((K ⊗[k] MvPolynomial σ k) ⧸ I.map
      (Algebra.TensorProduct.includeRight (R := k) (A := K)
        (B := MvPolynomial σ k))) ≃ₐ[K]
      MvPolynomial σ K ⧸ I.map (MvPolynomial.map (algebraMap k K)) :=
  Ideal.quotientEquivAlg (I.map
      (Algebra.TensorProduct.includeRight (R := k) (A := K)
        (B := MvPolynomial σ k)))
    (I.map (MvPolynomial.map (algebraMap k K)))
    (polynomialCoefficientTensorRingEquiv (k := k) (K := K) (σ := σ))
    (polynomialCoefficientTensorIdeal_map (k := k) (K := K) I)

/-- The quotient of a polynomial ring after coefficient extension is the
coefficient extension of its quotient, as an algebra over the larger field. -/
noncomputable def polynomialQuotientCoefficientTensorAlgEquiv
    (I : Ideal (MvPolynomial σ k)) :
    K ⊗[k] (MvPolynomial σ k ⧸ I) ≃ₐ[K]
      (MvPolynomial σ K ⧸ I.map (MvPolynomial.map (algebraMap k K))) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := k) K
      (MvPolynomial σ k) K I).trans
    (polynomialCoefficientTensorQuotientAlgEquiv I)

/-- Formula for coefficient extension on a polynomial quotient class. -/
theorem polynomialQuotientCoefficientTensorAlgEquiv_tmul_mk
    (I : Ideal (MvPolynomial σ k)) (a : K) (p : MvPolynomial σ k) :
    polynomialQuotientCoefficientTensorAlgEquiv I
      (a ⊗ₜ (Ideal.Quotient.mk I p)) =
      Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap k K)))
        (a • MvPolynomial.map (algebraMap k K) p) := by
  rw [polynomialQuotientCoefficientTensorAlgEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    polynomialCoefficientTensorQuotientAlgEquiv, Ideal.quotientEquivAlg_mk,
    polynomialCoefficientTensorRingEquiv,
    MvPolynomial.algebraTensorAlgEquiv_tmul]

end PfaffianDescent
