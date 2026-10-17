import PfaffianDescent.PolynomialCoefficientFaithfullyFlat
import PfaffianDescent.ProjectiveFiniteOfHilbertBound
import AllCharacteristics.GradedCoefficientMap
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Homogeneous quotient pieces under coefficient extension

This module begins the comparison of a homogeneous quotient with its scalar
extension, degree by degree.  The map is written directly on the actual
projective coordinate-ring components.
-/

namespace PfaffianDescent

open TensorProduct MvPolynomial AlgebraicGeometry
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective

universe u

variable {k K : Type u} {σ : Type} [Field k] [Field K] [Algebra k K]

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- The coefficient map on projective coordinate rings, viewed as a linear
map over the original coefficient field. -/
noncomputable def coordinateCoefficientMapLinear
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal) :
    AllCharacteristics.HomogeneousProjective.CoordinateRing I →ₗ[k]
      AllCharacteristics.HomogeneousProjective.CoordinateRing J :=
  { toFun := AllCharacteristics.HomogeneousProjective.coordinateCoefficientMap
      (algebraMap k K) I J hIJ
    map_add' := (AllCharacteristics.HomogeneousProjective.coordinateCoefficientMap
      (algebraMap k K) I J hIJ).map_add
    map_smul' := by
      intro r x
      induction x using Quotient.inductionOn' with
      | _ p =>
        simp only [Submodule.Quotient.mk''_eq_mk]
        rw [← Submodule.Quotient.mk_smul I.toIdeal,
          Ideal.Quotient.mk_eq_mk,
          AllCharacteristics.HomogeneousProjective.coordinateCoefficientMap_mk]
        rw [Ideal.Quotient.mk_eq_mk p,
          AllCharacteristics.HomogeneousProjective.coordinateCoefficientMap_mk]
        calc
          Submodule.Quotient.mk ((MvPolynomial.map (algebraMap k K)) (r • p)) =
              Submodule.Quotient.mk (r • (MvPolynomial.map (algebraMap k K)) p) :=
            congrArg (Submodule.Quotient.mk : MvPolynomial σ K →
              AllCharacteristics.HomogeneousProjective.CoordinateRing J)
              (by
                rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C,
                  ← MvPolynomial.smul_eq_C_mul]
                exact IsScalarTower.algebraMap_smul K r
                  ((MvPolynomial.map (algebraMap k K)) p))
          _ = r • Submodule.Quotient.mk ((MvPolynomial.map (algebraMap k K)) p) :=
            Submodule.Quotient.mk_smul J.toIdeal r _
          _ = r • Ideal.Quotient.mk J.toIdeal ((MvPolynomial.map (algebraMap k K)) p) :=
            congrArg (r • ·) (Ideal.Quotient.mk_eq_mk _) }

/-- Coefficient extension on one homogeneous component of a projective
coordinate quotient. -/
noncomputable def coefficientExtensionGradeMap
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (n : ℕ) : grading I n →ₗ[k] grading J n :=
  { toFun := fun x => ⟨coordinateCoefficientMapLinear I J hIJ x,
      AllCharacteristics.HomogeneousProjective.coordinateCoefficientMap_mem
        (algebraMap k K) I J hIJ x.property⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      exact (coordinateCoefficientMapLinear I J hIJ).map_add x y
    map_smul' := by
      intro r x
      apply Subtype.ext
      exact (coordinateCoefficientMapLinear I J hIJ).map_smul r x }

/-- The scalar extension of the degreewise coefficient map. -/
noncomputable def coefficientExtensionGradeTensorMap
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (n : ℕ) : K ⊗[k] grading I n →ₗ[K] grading J n :=
  LinearMap.liftBaseChange K (coefficientExtensionGradeMap I J hIJ n)

theorem coefficientExtensionGradeTensorMap_tmul
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (n : ℕ) (a : K) (x : grading I n) :
    coefficientExtensionGradeTensorMap I J hIJ n (a ⊗ₜ x) =
      a • coefficientExtensionGradeMap I J hIJ n x :=
  by
    change LinearMap.liftBaseChange K (coefficientExtensionGradeMap I J hIJ n)
      (a ⊗ₜ x) = _
    exact LinearMap.liftBaseChange_tmul (A := K)
      (coefficientExtensionGradeMap I J hIJ n) a x


/-- On a homogeneous class, the degreewise coefficient map has the expected
polynomial representative. -/
theorem coefficientExtensionGradeMap_mk
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (n : ℕ) (p : MvPolynomial σ k) (hp : p.IsHomogeneous n) :
    coefficientExtensionGradeMap I J hIJ n
      ⟨Ideal.Quotient.mk I.toIdeal p, ⟨p, hp, rfl⟩⟩ =
        ⟨Ideal.Quotient.mk J.toIdeal (MvPolynomial.map (algebraMap k K) p),
          AllCharacteristics.HomogeneousProjective.coordinateCoefficientMap_mem
            (algebraMap k K) I J hIJ ⟨p, hp, rfl⟩⟩ := by
  apply Subtype.ext
  exact AllCharacteristics.HomogeneousProjective.coordinateCoefficientMap_mk
    (algebraMap k K) I J hIJ p


/-- After inclusion in the full coordinate ring, coefficient extension of a
homogeneous quotient piece agrees with scalar extension of its inclusion. -/
theorem coefficientExtensionGradeTensorMap_subtype_comp
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (n : ℕ) :
    ((grading J n).subtype).comp (coefficientExtensionGradeTensorMap I J hIJ n) =
      ((Ideal.quotientEquivAlgOfEq K hIJ).toLinearEquiv.toLinearMap).comp
        (((polynomialQuotientCoefficientTensorAlgEquiv I.toIdeal).toLinearEquiv.toLinearMap).comp
          (AlgebraTensorModule.lTensor K K (grading I n).subtype)) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul a x =>
    simp only [LinearMap.comp_apply]
    rw [coefficientExtensionGradeTensorMap_tmul]
    obtain ⟨p, hp, hpx⟩ := x.property
    have hx : x = ⟨Ideal.Quotient.mk I.toIdeal p, ⟨p, hp, rfl⟩⟩ := by
      apply Subtype.ext
      exact hpx.symm
    subst x
    have hp' : p.IsHomogeneous n := hp
    rw [coefficientExtensionGradeMap_mk I J hIJ n p hp',
      AlgebraTensorModule.lTensor_tmul]
    change (grading J n).subtype
        (a • ⟨Ideal.Quotient.mk J.toIdeal (MvPolynomial.map (algebraMap k K) p), _⟩) =
      (Ideal.quotientEquivAlgOfEq K hIJ)
        (polynomialQuotientCoefficientTensorAlgEquiv I.toIdeal
          (a ⊗ₜ Ideal.Quotient.mk I.toIdeal p))
    rw [polynomialQuotientCoefficientTensorAlgEquiv_tmul_mk,
      Ideal.quotientEquivAlgOfEq_mk]
    change a • Ideal.Quotient.mk J.toIdeal (MvPolynomial.map (algebraMap k K) p) =
      Ideal.Quotient.mk J.toIdeal (a • MvPolynomial.map (algebraMap k K) p)
    calc
      a • Ideal.Quotient.mk J.toIdeal (MvPolynomial.map (algebraMap k K) p) =
          a • Submodule.Quotient.mk (MvPolynomial.map (algebraMap k K) p) :=
        congrArg (a • ·) (Ideal.Quotient.mk_eq_mk _).symm
      _ = Submodule.Quotient.mk (a • MvPolynomial.map (algebraMap k K) p) :=
        (Submodule.Quotient.mk_smul J.toIdeal a _).symm
      _ = Ideal.Quotient.mk J.toIdeal (a • MvPolynomial.map (algebraMap k K) p) :=
        Ideal.Quotient.mk_eq_mk _


/-- Scalar extension is injective on every homogeneous quotient component
when the target ideal is the coefficient extension of the source ideal. -/
theorem coefficientExtensionGradeTensorMap_injective
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (n : ℕ) :
    Function.Injective (coefficientExtensionGradeTensorMap I J hIJ n) := by
  let L : K ⊗[k] grading I n →ₗ[K]
      K ⊗[k] AllCharacteristics.HomogeneousProjective.CoordinateRing I :=
    AlgebraTensorModule.lTensor (R := k) K K (grading I n).subtype
  let E : K ⊗[k] AllCharacteristics.HomogeneousProjective.CoordinateRing I →ₗ[K]
      MvPolynomial σ K ⧸ I.toIdeal.map (MvPolynomial.map (algebraMap k K)) :=
    (polynomialQuotientCoefficientTensorAlgEquiv I.toIdeal).toLinearEquiv.toLinearMap
  let Q : MvPolynomial σ K ⧸ I.toIdeal.map (MvPolynomial.map (algebraMap k K)) →ₗ[K]
      AllCharacteristics.HomogeneousProjective.CoordinateRing J :=
    (Ideal.quotientEquivAlgOfEq K hIJ).toLinearEquiv.toLinearMap
  have hsub : Function.Injective L := by
    change Function.Injective (LinearMap.lTensor K (grading I n).subtype)
    exact (Module.FaithfullyFlat.lTensor_injective_iff_injective k K
      (grading I n).subtype).mpr (grading I n).subtype_injective
  have hE : Function.Injective E :=
    (polynomialQuotientCoefficientTensorAlgEquiv I.toIdeal).toLinearEquiv.injective
  have hQ : Function.Injective Q :=
    (Ideal.quotientEquivAlgOfEq K hIJ).toLinearEquiv.injective
  have hright : Function.Injective (Q.comp (E.comp L)) :=
    hQ.comp (hE.comp hsub)
  have hleft : Function.Injective
      (((grading J n).subtype).comp (coefficientExtensionGradeTensorMap I J hIJ n)) := by
    rw [coefficientExtensionGradeTensorMap_subtype_comp]
    exact hright
  intro x y hxy
  apply hleft
  simp only [LinearMap.comp_apply, hxy]


/-- The homogeneous quotient pieces cannot grow under faithfully flat
coefficient descent. -/
theorem grade_finrank_le_coefficientExtension
    [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (n : ℕ) :
    Module.finrank k (grading I n) ≤ Module.finrank K (grading J n) := by
  letI : Module.Finite K (grading J n) := by
    apply Module.Finite.iff_fg.mpr
    exact (MvPolynomial.homogeneousSubmodule_fg σ K n).map
      (Ideal.Quotient.mkₐ K J.toIdeal).toLinearMap
  rw [← Module.finrank_baseChange (R := K) (S := k) (M' := grading I n)]
  exact LinearMap.finrank_le_finrank_of_injective
    (coefficientExtensionGradeTensorMap_injective I J hIJ n)


/-- An eventual Hilbert-function bound after a field coefficient extension
already makes the projective scheme over the ground field finite. -/
theorem projective_finite_of_coefficientExtension_hilbert_bound
    [Finite σ]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal)
    (N D : ℕ)
    (hJ : ∀ n, N ≤ n → Module.finrank K (grading J n) ≤ D) :
    IsFinite (AllCharacteristics.HomogeneousProjective.toBase I) := by
  apply projective_finite_of_hilbert_bound I N D
  intro n hn
  exact (grade_finrank_le_coefficientExtension I J hIJ n).trans (hJ n hn)

end PfaffianDescent
