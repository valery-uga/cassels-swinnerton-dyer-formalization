import AllCharacteristics.GradedCoefficientMap
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Arbitrary coefficient base change of projective coordinate rings

Extending the coefficients of a homogeneous polynomial quotient agrees with
tensoring its coordinate ring over the coefficient ring. This holds even
when the new coefficient algebra is neither flat nor a domain, as needed
for residue-field and base-ideal fibres of Voisin's family.
-/

namespace PfaffianDescent

open MvPolynomial TensorProduct
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
variable (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) S))
variable (hJC : J.toIdeal.map (MvPolynomial.map (algebraMap R S)) = C.toIdeal)

private theorem polynomialTensorIdeal_map
    (I : Ideal (MvPolynomial (Fin 4) R)) :
    I.map (MvPolynomial.map (algebraMap R S)) =
      (I.map (Algebra.TensorProduct.includeRight (R := R) (A := S)
        (B := MvPolynomial (Fin 4) R))).map
        (↑(MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) R S) :
          S ⊗[R] MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 4) S) := by
  let E := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) R S
  have hcomp : (↑E : S ⊗[R] MvPolynomial (Fin 4) R →+*
      MvPolynomial (Fin 4) S).comp
      (↑(Algebra.TensorProduct.includeRight (R := R) (A := S)
        (B := MvPolynomial (Fin 4) R)) : MvPolynomial (Fin 4) R →+*
          S ⊗[R] MvPolynomial (Fin 4) R) =
      MvPolynomial.map (algebraMap R S) := by
    apply RingHom.ext
    intro p
    change E (1 ⊗ₜ p) = MvPolynomial.map (algebraMap R S) p
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  calc
    I.map (MvPolynomial.map (algebraMap R S)) = I.map
        ((↑E : S ⊗[R] MvPolynomial (Fin 4) R →+*
          MvPolynomial (Fin 4) S).comp
          (↑(Algebra.TensorProduct.includeRight (R := R) (A := S)
            (B := MvPolynomial (Fin 4) R)) : MvPolynomial (Fin 4) R →+*
              S ⊗[R] MvPolynomial (Fin 4) R)) :=
      congrArg I.map hcomp.symm
    _ = (I.map (Algebra.TensorProduct.includeRight (R := R) (A := S)
      (B := MvPolynomial (Fin 4) R))).map
        (↑(MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) R S) :
          S ⊗[R] MvPolynomial (Fin 4) R →+* MvPolynomial (Fin 4) S) :=
      (Ideal.map_map _ _).symm

/-- Arbitrary coefficient extension of an actual homogeneous coordinate
quotient is its tensor product over the original coefficient ring. -/
noncomputable def coordinateRingTensorAlgEquiv :
    S ⊗[R] CoordinateRing J ≃ₐ[S] CoordinateRing C :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S
      (MvPolynomial (Fin 4) R) S J.toIdeal).trans
    ((Ideal.quotientEquivAlg
      (J.toIdeal.map (Algebra.TensorProduct.includeRight (R := R)
        (A := S) (B := MvPolynomial (Fin 4) R)))
      (J.toIdeal.map (MvPolynomial.map (algebraMap R S)))
      (MvPolynomial.algebraTensorAlgEquiv (σ := Fin 4) R S)
      (polynomialTensorIdeal_map J.toIdeal)).trans
      (Ideal.quotientEquivAlgOfEq S hJC))

/-- The tensor equivalence sends a polynomial class to the class of the
coefficient-changed polynomial, with the tensor scalar acting normally. -/
theorem coordinateRingTensorAlgEquiv_tmul_mk
    (a : S) (p : MvPolynomial (Fin 4) R) :
    coordinateRingTensorAlgEquiv J C hJC
      (a ⊗ₜ Ideal.Quotient.mk J.toIdeal p) =
      Ideal.Quotient.mk C.toIdeal
        (a • MvPolynomial.map (algebraMap R S) p) := by
  rw [coordinateRingTensorAlgEquiv,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, Ideal.quotientEquivAlgOfEq_mk,
    MvPolynomial.algebraTensorAlgEquiv_tmul]

/-- On an arbitrary coordinate-ring class, the tensor inclusion is the
usual coefficient-change map. -/
theorem coordinateRingTensorAlgEquiv_one_tmul
    (x : CoordinateRing J) :
    coordinateRingTensorAlgEquiv J C hJC (1 ⊗ₜ[R] x) =
      coordinateCoefficientMap (algebraMap R S) J C hJC x := by
  induction x using Quotient.inductionOn' with
  | _ p =>
    simp only [Submodule.Quotient.mk''_eq_mk, Ideal.Quotient.mk_eq_mk]
    rw [coordinateRingTensorAlgEquiv_tmul_mk,
      coordinateCoefficientMap_mk, one_smul]

end PfaffianDescent
