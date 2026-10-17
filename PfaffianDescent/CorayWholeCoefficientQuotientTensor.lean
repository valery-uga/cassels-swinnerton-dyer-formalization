import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import PfaffianDescent.ProjectiveCoefficientIdealMap

/- SOURCE ONLY152; no compiler, options, or limit changes. -/

/- Source snapshot: /private/tmp/cassels-coray-whole-generic-cut-source152/new/PfaffianDescent/CorayWholeCoefficientQuotientTensor.lean -/
/-! SOURCE ONLY / UNVERIFIED152. Literal whole coefficient quotient equals
the native scalar extension of the original whole quotient as an ALGEBRA.
The ideal comparison is proved from actual polynomial tensor generators. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial TensorProduct
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
variable {K E : Type u} [Field K] [Field E] [Algebra K E]
attribute [local instance] MvPolynomial.algebraMvPolynomial MvPolynomial.gradedAlgebra

/-- The actual native polynomial tensor equivalence sends the extended whole
original ideal to EXACTLY the literal coefficient-extended ideal. -/
theorem wholeCoefficientTensorIdeal_map_eq (C : Ideal (MvPolynomial (Fin 4) K)) :
    (C.map (Algebra.TensorProduct.includeRight (R := K) (A := E))).map
      (MvPolynomial.algebraTensorAlgEquiv K E).toRingHom =
        C.map (MvPolynomial.map (algebraMap K E)) := by
  have h : (MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) K E).toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := K) (A := E)).toRingHom =
      MvPolynomial.map (algebraMap K E) := by
    apply RingHom.ext
    intro p
    change MvPolynomial.algebraTensorAlgEquiv K E (1 ⊗ₜ[K] p) =
      MvPolynomial.map (algebraMap K E) p
    simp only [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  exact (Ideal.map_map (I := C)
    (Algebra.TensorProduct.includeRight (R := K) (A := E)).toRingHom
    (MvPolynomial.algebraTensorAlgEquiv K E).toRingHom).trans
      (congrArg (fun f : MvPolynomial (Fin 4) K →+* MvPolynomial (Fin 4) E => C.map f) h)

/-- Whole original coordinate quotient, coefficient-extended without choosing
any component, is the native tensor algebra of the original quotient. -/
def wholeCoefficientQuotientTensorAlgEquiv (C : Ideal (MvPolynomial (Fin 4) K)) :
    E ⊗[K] (MvPolynomial (Fin 4) K ⧸ C) ≃ₐ[E]
      MvPolynomial (Fin 4) E ⧸ C.map (MvPolynomial.map (algebraMap K E)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := K) E
    (MvPolynomial (Fin 4) K) E C).trans
      (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv K E)
        (wholeCoefficientTensorIdeal_map_eq C).symm)

/-- The actual quotient tensor equivalence has its exact literal polynomial
formula, including arbitrary parameter-field coefficients. -/
theorem wholeCoefficientQuotientTensorAlgEquiv_tmul_mk
    (C : Ideal (MvPolynomial (Fin 4) K)) (a : E) (p : MvPolynomial (Fin 4) K) :
    wholeCoefficientQuotientTensorAlgEquiv (E := E) C
      (a ⊗ₜ[K] Ideal.Quotient.mk C p) =
        Ideal.Quotient.mk (C.map (MvPolynomial.map (algebraMap K E)))
          (a • p.map (algebraMap K E)) := by
  change Ideal.Quotient.mk (C.map (MvPolynomial.map (algebraMap K E)))
    (MvPolynomial.algebraTensorAlgEquiv K E (a ⊗ₜ[K] p)) = _
  exact congrArg (Ideal.Quotient.mk (C.map (MvPolynomial.map (algebraMap K E))))
    (MvPolynomial.algebraTensorAlgEquiv_tmul K E a p)

/-- The actual homogeneous whole coefficient extension has exactly that same
native tensor algebra; no ideal equality certificate is supplied. -/
def wholeHomogeneousCoefficientQuotientTensorAlgEquiv
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) :
    E ⊗[K] CoordinateRing C ≃ₐ[E]
      CoordinateRing (PfaffianDescent.coefficientChangedHomogeneousIdeal (algebraMap K E) C) := by
  exact (wholeCoefficientQuotientTensorAlgEquiv (E := E) C.toIdeal).trans
    (Ideal.quotientEquivAlgOfEq E
      (PfaffianDescent.coefficientChangedHomogeneousIdeal_toIdeal (algebraMap K E) C))

end PfaffianDescent.Coray

/- Exported types and recursive standard axioms roots for this bounded frontier. -/
