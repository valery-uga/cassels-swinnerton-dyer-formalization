import PfaffianDescent.ProjectiveCoefficientGradeBaseChange
import AllCharacteristics.UniversalHomogeneous
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
SOURCE ONLY / UNVERIFIED. General whole-ideal homogeneous quotient grade
invariance. All coefficient ideals are retained, including nilpotents.
-/

noncomputable section
namespace PfaffianDescent
open MvPolynomial Module TensorProduct
open scoped TensorProduct
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous
universe u
variable {k K : Type u} {σ : Type} [Field k] [Field K] [Algebra k K] [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra MvPolynomial.algebraMvPolynomial

private def polynomialGradeCoefficientMap (d : ℕ) :
    homogeneousSubmodule σ k d →ₗ[k] homogeneousSubmodule σ K d where
  toFun p := ⟨MvPolynomial.map (algebraMap k K) p.val, p.property.map _⟩
  map_add' p q := Subtype.ext (map_add _ _ _)
  map_smul' a p := by
    apply Subtype.ext
    change MvPolynomial.map (algebraMap k K) (a • p.val) =
      a • MvPolynomial.map (algebraMap k K) p.val
    calc
      MvPolynomial.map (algebraMap k K) (a • p.val) =
          (algebraMap k K a) • MvPolynomial.map (algebraMap k K) p.val := by
        simp only [smul_eq_C_mul, map_mul, map_C]
      _ = a • MvPolynomial.map (algebraMap k K) p.val :=
        IsScalarTower.algebraMap_smul K a _

private def polynomialGradeCoefficientTensorMap (d : ℕ) :
    K ⊗[k] homogeneousSubmodule σ k d →ₗ[K] homogeneousSubmodule σ K d :=
  LinearMap.liftBaseChange K (polynomialGradeCoefficientMap (k := k) (K := K) d)

private theorem polynomialGradeCoefficientTensorMap_surjective (d : ℕ) :
    Function.Surjective
      (polynomialGradeCoefficientTensorMap (k := k) (K := K) (σ := σ) d) := by
  intro p
  let q : Monomials σ d → homogeneousSubmodule σ k d :=
    fun m => ⟨MvPolynomial.monomial m.val 1, MvPolynomial.isHomogeneous_monomial _ m.property⟩
  let z : K ⊗[k] homogeneousSubmodule σ k d :=
    ∑ m : Monomials σ d, p.val.coeff m.val ⊗ₜ q m
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change ((polynomialGradeCoefficientTensorMap (k := k) (K := K) d)
      (∑ m : Monomials σ d, p.val.coeff m.val ⊗ₜ q m)).val = p.val
  rw [map_sum]
  simp only [polynomialGradeCoefficientTensorMap, LinearMap.liftBaseChange_tmul]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  change ∑ m : Monomials σ d, p.val.coeff m.val •
      (polynomialGradeCoefficientMap (k := k) (K := K) d (q m)).val = p.val
  dsimp [polynomialGradeCoefficientMap, q]
  simp only [MvPolynomial.map_monomial, map_one]
  rw [show (fun m : Monomials σ d => p.val.coeff m.val •
      MvPolynomial.monomial m.val (1 : K)) = fun m =>
        MvPolynomial.monomial m.val (p.val.coeff m.val) by
      funext m
      rw [MvPolynomial.smul_monomial]
      simp]
  exact sum_monomial_coeff_eq p.val p.property

private def homogeneousGradeProjection
    {F : Type u} [Field F]
    (I : HomogeneousIdeal (homogeneousSubmodule σ F)) (d : ℕ) :
    homogeneousSubmodule σ F d →ₗ[F] grading I d where
  toFun p := ⟨Ideal.Quotient.mk I.toIdeal p.1, ⟨p.1, p.2, rfl⟩⟩
  map_add' p q := Subtype.ext (map_add (Ideal.Quotient.mk I.toIdeal) p.1 q.1)
  map_smul' a p := Subtype.ext (map_smul (Ideal.Quotient.mkₐ F I.toIdeal) a p.1)

private theorem homogeneousGradeCoefficientTensor_square
    (I : HomogeneousIdeal (homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal) (d : ℕ) :
    (homogeneousGradeProjection J d).comp
        (polynomialGradeCoefficientTensorMap (k := k) (K := K) d) =
      (coefficientExtensionGradeTensorMap I J hIJ d).comp
        (AlgebraTensorModule.lTensor K K (homogeneousGradeProjection I d)) := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul a p =>
    have hamb : polynomialGradeCoefficientTensorMap
        (k := k) (K := K) d (a ⊗ₜ[k] p) =
        a • polynomialGradeCoefficientMap (k := k) (K := K) d p :=
      LinearMap.liftBaseChange_tmul (A := K)
        (polynomialGradeCoefficientMap (k := k) (K := K) d) a p
    simp only [LinearMap.comp_apply]
    rw [AlgebraTensorModule.lTensor_tmul,
      coefficientExtensionGradeTensorMap_tmul, hamb, map_smul]
    apply Subtype.ext
    change a • Ideal.Quotient.mk J.toIdeal (MvPolynomial.map (algebraMap k K) p.1) =
      a • coordinateCoefficientMap (algebraMap k K) I J hIJ
        (Ideal.Quotient.mk I.toIdeal p.1)
    rw [coordinateCoefficientMap_mk]

/-- The actual coefficient tensor map on homogeneous quotient components is
surjective for any finite set of variables. -/
theorem coefficientExtensionGradeTensorMap_surjective
    (I : HomogeneousIdeal (homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal) (d : ℕ) :
    Function.Surjective (coefficientExtensionGradeTensorMap I J hIJ d) := by
  intro y
  obtain ⟨q, hqhom, hq⟩ := y.2
  obtain ⟨z, hz⟩ := polynomialGradeCoefficientTensorMap_surjective
    (k := k) (K := K) d (⟨q, hqhom⟩ : homogeneousSubmodule σ K d)
  refine ⟨AlgebraTensorModule.lTensor K K (homogeneousGradeProjection I d) z, ?_⟩
  have hsquare := (LinearMap.congr_fun
    (homogeneousGradeCoefficientTensor_square I J hIJ d) z).symm
  change coefficientExtensionGradeTensorMap I J hIJ d
      (AlgebraTensorModule.lTensor K K (homogeneousGradeProjection I d) z) =
    homogeneousGradeProjection J d
      (polynomialGradeCoefficientTensorMap (k := k) (K := K) d z) at hsquare
  rw [hz] at hsquare
  exact hsquare.trans (Subtype.ext hq)

/-- Whole homogeneous ideals give scalar extension equivalences on every
actual quotient component. -/
def coefficientExtensionGradeTensorLinearEquiv
    (I : HomogeneousIdeal (homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal) (d : ℕ) :
    K ⊗[k] grading I d ≃ₗ[K] grading J d :=
  LinearEquiv.ofBijective (coefficientExtensionGradeTensorMap I J hIJ d)
    ⟨coefficientExtensionGradeTensorMap_injective I J hIJ d,
      coefficientExtensionGradeTensorMap_surjective I J hIJ d⟩

/-- Every actual homogeneous quotient Hilbert value is invariant under
literal whole-ideal coefficient extension. -/
theorem grade_finrank_eq_coefficientExtension
    (I : HomogeneousIdeal (homogeneousSubmodule σ k))
    (J : HomogeneousIdeal (homogeneousSubmodule σ K))
    (hIJ : I.toIdeal.map (MvPolynomial.map (algebraMap k K)) = J.toIdeal) (d : ℕ) :
    finrank K (grading J d) = finrank k (grading I d) := by
  rw [← (coefficientExtensionGradeTensorLinearEquiv I J hIJ d).finrank_eq]
  exact Module.finrank_baseChange (R := K) (S := k) (M' := grading I d)

end PfaffianDescent
