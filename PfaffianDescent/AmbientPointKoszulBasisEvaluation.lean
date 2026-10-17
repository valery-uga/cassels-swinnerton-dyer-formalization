import PfaffianDescent.AmbientPointKoszulBasisExistence

/-! # Actual normalized point evaluation in a centered homogeneous basis -/

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
theorem ambientPointKoszul_basis_eval
    (M : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K) (i : Fin 4) :
    eval₂Hom (RingHom.id K) v (ambientPointKoszul_basis M i).val = M.mulVec v i := by
  rw [ambientPointKoszul_basis_coe]
  exact linearCoordinate_eval M v i

theorem ambientPointKoszul_basis_eval_zero_one
    (M : Matrix (Fin 4) (Fin 4) K) (v : Fin 4 → K)
    (hMv : M.mulVec v = ambientPointKoszul_vector K) :
    eval₂Hom (RingHom.id K) v (ambientPointKoszul_basis M 0).val = 1 :=
  (ambientPointKoszul_basis_eval M v 0).trans (congrFun hMv 0)

set_option backward.isDefEq.respectTransparency false in
/-- Transported affine-origin restriction agrees with actual homogeneous
evaluation at any vector whose basis values are `[1,0,0,0]`. -/
theorem ambientPointKoszul_basisChartMap_eq_evaluation
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (v : Fin 4 → K)
    (hMv : M.mulVec v = ambientPointKoszul_vector K) :
    ambientPointKoszul_basisChartMap M hM =
      AllCharacteristics.GradedChart.liftCoordinateOne PS (ambientPointKoszul_basis M 0).val
        (eval₂Hom (RingHom.id K) v) (ambientPointKoszul_basis_eval_zero_one M v hMv) := by
  symm
  apply ambientPointKoszul_basisChartMap_unique M hM
  · intro a
    exact (AllCharacteristics.GradedChart.liftCoordinateOne_baseMap PS
      (ambientPointKoszul_basis M 0).val (eval₂Hom (RingHom.id K) v) _ a).trans
        (eval₂Hom_C _ _ a)
  · intro i
    have h := AllCharacteristics.GradedChart.liftCoordinateOne_normalized PS
      (ambientPointKoszul_basis M 0).val (eval₂Hom (RingHom.id K) v)
      (ambientPointKoszul_basis_eval_zero_one M v hMv) (ambientPointKoszul_basis M 0).property
      (ambientPointKoszul_basis M i.succ).val (ambientPointKoszul_basis M i.succ).property
    have hi : ambientPointKoszul_vector K i.succ = 0 := by fin_cases i <;> rfl
    exact h.trans ((ambientPointKoszul_basis_eval M v i.succ).trans ((congrFun hMv i.succ).trans hi))

set_option backward.isDefEq.respectTransparency false in
/-- The actual basis point is the actual native homogeneous-evaluation
point of its centered vector, with no scheme-map comparison premise. -/
theorem ambientPointKoszul_basisPoint_eq_evaluation
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (v : Fin 4 → K)
    (hMv : M.mulVec v = ambientPointKoszul_vector K) :
    ambientPointKoszul_basisPoint M hM =
      Spec.map (CommRingCat.ofHom
        (AllCharacteristics.GradedChart.liftCoordinateOne PS (ambientPointKoszul_basis M 0).val
          (eval₂Hom (RingHom.id K) v) (ambientPointKoszul_basis_eval_zero_one M v hMv))) ≫
        Proj.awayι PS (ambientPointKoszul_basis M 0).val
          (ambientPointKoszul_basis M 0).property (by decide : 0 < 1) := by
  unfold ambientPointKoszul_basisPoint
  rw [ambientPointKoszul_basisChartMap_eq_evaluation M hM v hMv]

end PfaffianDescent
