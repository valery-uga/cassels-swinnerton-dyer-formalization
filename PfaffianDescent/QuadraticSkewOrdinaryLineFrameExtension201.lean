import PfaffianDescent.BasisMatchingProjectorWholeUnionIdeal
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! SOURCE ONLY / UNCOMPILED. Construct the compatible geometric ambient
frame by scalar extension of an ordinary coefficient-field basis. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.OrdinaryLines201
open Module QuarticNet
universe u
variable {E K : Type u} [Field E] [Field K]

theorem coefficientExtension_exists_same_projector_frame201
    (f : E →+* K) (C : Basis (Fin 4) E (Fin 4 → E)) :
    ∃ B : Basis (Fin 4) K (Fin 4 → K),
      basisCoordinateMatrix B = (basisCoordinateMatrix C).map f ∧
      (matchingEdgeProjectorMatrix C).map f = matchingEdgeProjectorMatrix B := by
  classical
  let M := basisCoordinateMatrix C
  let A := M.map f
  let A' := (M⁻¹).map f
  have hLeft : A' * A = 1 := by
    change (M⁻¹).map f * M.map f = 1
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul M (basisCoordinateMatrix_isUnit C),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hRight : A * A' = 1 := by
    change M.map f * (M⁻¹).map f = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv M (basisCoordinateMatrix_isUnit C),
      Matrix.map_one _ (map_zero _) (map_one _)]
  let e := Matrix.toLin'OfInv hLeft hRight
  let B := (Pi.basisFun K (Fin 4)).map e
  have hB : basisCoordinateMatrix B = A := by
    ext i j
    change e (Pi.basisFun K (Fin 4) j) i = A i j
    rw [Pi.basisFun_apply]
    change A.mulVec (Pi.single j 1) i = A i j
    exact congrFun (Matrix.mulVec_single_one A j) i
  have hInv : A⁻¹ = A' := Matrix.inv_eq_left_inv hLeft
  have hD : (Matrix.diagonal ![1, 1, 0, 0] : Matrix (Fin 4) (Fin 4) E).map f =
      (Matrix.diagonal ![1, 1, 0, 0] : Matrix (Fin 4) (Fin 4) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply, Matrix.diagonal]
  refine ⟨B, hB, ?_⟩
  rw [matchingEdgeProjectorMatrix_factor C, matchingEdgeProjectorMatrix_factor B, hB,
    hInv, Matrix.map_mul, Matrix.map_mul, hD]

end PfaffianDescent.QuadraticSkewRationality.OrdinaryLines201
