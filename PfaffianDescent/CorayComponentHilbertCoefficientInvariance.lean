import PfaffianDescent.ProjectiveCoefficientGradeBaseChange
import PfaffianDescent.HomogeneousIdealPieceCoefficientBaseChange
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Literal whole-ideal coefficient extension preserves actual Hilbert functions

The existing actual quotient grade tensor map is injective. Here its missing
surjectivity is DERIVED from the actual polynomial homogeneous tensor map and
the actual quotient projections. No desired slope, degree, generator descent,
or quotient-grade surjectivity certificate is supplied.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module TensorProduct
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective
universe u
variable {k K : Type u} [Field k] [Field K] [Algebra k K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial

private def actualGradeProjection
    {F : Type u} [Field F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (d : ℕ) :
    homogeneousSubmodule (Fin 4) F d →ₗ[F] grading I d where
  toFun p := ⟨Ideal.Quotient.mk I.toIdeal p.1, ⟨p.1, p.2, rfl⟩⟩
  map_add' p q := Subtype.ext (map_add (Ideal.Quotient.mk I.toIdeal) p.1 q.1)
  map_smul' a p := Subtype.ext (map_smul (Ideal.Quotient.mkₐ F I.toIdeal) a p.1)

private theorem actualGradeCoefficientTensor_square
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal) (d : ℕ) :
    (actualGradeProjection J d).comp
        (PfaffianDescent.homogeneousIdealPieceAmbientCoefficientTensorMap (k := k) (K := K) d) =
      (PfaffianDescent.coefficientExtensionGradeTensorMap I J hIJ d).comp
        (AlgebraTensorModule.lTensor K K (actualGradeProjection I d)) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a p =>
    have hamb : PfaffianDescent.homogeneousIdealPieceAmbientCoefficientTensorMap
        (k := k) (K := K) d (a ⊗ₜ[k] p) =
        a • PfaffianDescent.homogeneousIdealPieceAmbientCoefficientMap (k := k) (K := K) d p :=
      LinearMap.liftBaseChange_tmul (A := K)
        (PfaffianDescent.homogeneousIdealPieceAmbientCoefficientMap (k := k) (K := K) d) a p
    simp only [LinearMap.comp_apply]
    rw [AlgebraTensorModule.lTensor_tmul,
      PfaffianDescent.coefficientExtensionGradeTensorMap_tmul, hamb, map_smul]
    apply Subtype.ext
    change a • Ideal.Quotient.mk J.toIdeal (MvPolynomial.map (algebraMap k K) p.1) =
      a • coordinateCoefficientMap (algebraMap k K) I J hIJ
        (Ideal.Quotient.mk I.toIdeal p.1)
    rw [coordinateCoefficientMap_mk]

/-- Actual homogeneous polynomial spanning DERIVES surjectivity of the literal
quotient-grade tensor map under arbitrary FIELD coefficient extension. -/
theorem actualComponentGradeCoefficientTensor_surjective
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal) (d : ℕ) :
    Function.Surjective (PfaffianDescent.coefficientExtensionGradeTensorMap I J hIJ d) := by
  intro y
  obtain ⟨q, hqhom, hq⟩ := y.2
  obtain ⟨z, hz⟩ := PfaffianDescent.homogeneousIdealPieceAmbientCoefficientTensorMap_surjective
    (k := k) (K := K) d (⟨q, hqhom⟩ : homogeneousSubmodule (Fin 4) K d)
  refine ⟨AlgebraTensorModule.lTensor K K (actualGradeProjection I d) z, ?_⟩
  have hsquare := (LinearMap.congr_fun (actualGradeCoefficientTensor_square I J hIJ d) z).symm
  change PfaffianDescent.coefficientExtensionGradeTensorMap I J hIJ d
      (AlgebraTensorModule.lTensor K K (actualGradeProjection I d) z) =
    actualGradeProjection J d
      (PfaffianDescent.homogeneousIdealPieceAmbientCoefficientTensorMap (k := k) (K := K) d z)
      at hsquare
  rw [hz] at hsquare
  exact hsquare.trans (Subtype.ext hq)

/-- The SAME actual whole-ideal coefficient extension gives the literal
homogeneous quotient tensor equivalence in every degree. -/
def actualComponentGradeCoefficientTensorLinearEquiv
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal) (d : ℕ) :
    K ⊗[k] grading I d ≃ₗ[K] grading J d :=
  LinearEquiv.ofBijective (PfaffianDescent.coefficientExtensionGradeTensorMap I J hIJ d)
    ⟨PfaffianDescent.coefficientExtensionGradeTensorMap_injective I J hIJ d,
      actualComponentGradeCoefficientTensor_surjective I J hIJ d⟩

/-- Every actual coordinate Hilbert value is unchanged by literal whole-ideal
FIELD coefficient extension. This compares curve dimensions, not field degree. -/
theorem actualComponentGrade_finrank_eq_coefficientExtension
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal) (d : ℕ) :
    finrank K (grading J d) = finrank k (grading I d) := by
  rw [← (actualComponentGradeCoefficientTensorLinearEquiv I J hIJ d).finrank_eq]
  exact Module.finrank_baseChange (R := K) (S := k) (M' := grading I d)

end PfaffianDescent.Coray
