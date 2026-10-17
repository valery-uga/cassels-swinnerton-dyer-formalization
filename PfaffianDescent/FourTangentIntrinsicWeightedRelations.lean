import PfaffianDescent.FourTangentIntrinsicQuadraticSystem

/-! The weighted skew criterion for the FULL intrinsic quadratic system of
the actual four tangent double points, rather than only its coordinate model. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fourTangent_intrinsicQuadraticSystem_finrank_ge_three_iff
    {K : Type u} [Field K]
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ i, U i i = 0) :
    3 ≤ finrank K (intrinsicFullQuadraticSystem
      (fourTangentDualToProjective U ≫ quotientProjMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))) ↔
      ∃ w : Fin 4 → K, w ≠ 0 ∧
        ∀ i j, i < j → w i * U i j = -(w j * U j i) := by
  rw [fourTangent_intrinsicQuadraticSystem_eq_tangentKernel U hdiag,
    fullTangentQuadric_finrank U hdiag,
    three_le_finrank_ker_tangentQuadricEvaluation_iff]
  constructor
  · rintro ⟨w, hw, h01, h02, h03, h12, h13, h23⟩
    refine ⟨w, hw, ?_⟩
    intro i j hij
    fin_cases i <;> fin_cases j <;> norm_num at hij
    · exact add_eq_zero_iff_eq_neg.mp h01
    · exact add_eq_zero_iff_eq_neg.mp h02
    · exact add_eq_zero_iff_eq_neg.mp h03
    · exact add_eq_zero_iff_eq_neg.mp h12
    · exact add_eq_zero_iff_eq_neg.mp h13
    · exact add_eq_zero_iff_eq_neg.mp h23
  · rintro ⟨w, hw, h⟩
    exact ⟨w, hw,
      add_eq_zero_iff_eq_neg.mpr (h 0 1 (by decide)),
      add_eq_zero_iff_eq_neg.mpr (h 0 2 (by decide)),
      add_eq_zero_iff_eq_neg.mpr (h 0 3 (by decide)),
      add_eq_zero_iff_eq_neg.mpr (h 1 2 (by decide)),
      add_eq_zero_iff_eq_neg.mpr (h 1 3 (by decide)),
      add_eq_zero_iff_eq_neg.mpr (h 2 3 (by decide))⟩

end PfaffianDescent.QuarticNet
