import PfaffianDescent.CorayWholeIdealGradeRestriction
import PfaffianDescent.CorayComponentHilbertFunctionBound
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! SOURCE ONLY. Rank-nullity for the
whole ideal in the same homogeneous quotient ring. -/
noncomputable section
namespace PfaffianDescent.Coray
open MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- Actual quotient-grade kernel equals the literal whole ideal grade.
Both sides keep the same coordinate class, with no saturation or radical. -/
def homogeneousQuotientGradeKernelWholeIdealEquiv
    (I J : HomogeneousIdeal PS) (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) :
    (homogeneousCoordinateQuotientGradeMap I J hIJ d).ker ≃ₗ[K]
      wholeIdealGrade (grading I) (J.toIdeal.map (Ideal.Quotient.mk I.toIdeal)) d := by
  let r := homogeneousCoordinateQuotientGradeMap I J hIJ d
  have hiff (x : grading I d) : r x = 0 ↔
      x.val ∈ J.toIdeal.map (Ideal.Quotient.mk I.toIdeal) := by
    rw [← Ideal.Quotient.factor_ker hIJ]
    change r x = 0 ↔ (Ideal.Quotient.factor hIJ) x.val = 0
    constructor
    · intro hx; exact congrArg Subtype.val hx
    · intro hx; exact Subtype.ext hx
  refine
    { toFun := fun x => ⟨x.val.val, (hiff x.val).mp x.property, x.val.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.2⟩, (hiff ⟨x.val, x.property.2⟩).mpr x.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

/-- Genuine rank-nullity for the literal component ideal in its ambient
surface coordinate ring, from the actual surjective quotient-grade map. -/
theorem homogeneousQuotientGrade_finrank_add_wholeIdealGrade
    (I J : HomogeneousIdeal PS) (hIJ : I.toIdeal ≤ J.toIdeal) (d : ℕ) :
    finrank K (grading J d) +
      finrank K (wholeIdealGrade (grading I) (J.toIdeal.map (Ideal.Quotient.mk I.toIdeal)) d) =
        finrank K (grading I d) := by
  letI : Module.Finite K (grading I d) := by
    change Module.Finite K ((PS d).map (Ideal.Quotient.mkₐ K I.toIdeal).toLinearMap)
    infer_instance
  let r := homogeneousCoordinateQuotientGradeMap I J hIJ d
  have h := r.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr
    (homogeneousCoordinateQuotientGradeMap_surjective I J hIJ d), finrank_top,
    (homogeneousQuotientGradeKernelWholeIdealEquiv I J hIJ d).finrank_eq] at h
  exact h


end PfaffianDescent.Coray
