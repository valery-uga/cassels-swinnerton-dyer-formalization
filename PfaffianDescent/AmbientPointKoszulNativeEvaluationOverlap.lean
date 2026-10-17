import PfaffianDescent.AmbientPointKoszulBasisEvaluation

/-! # Native projective evaluation is independent of the normalizing linear form -/

noncomputable section
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial

namespace PfaffianDescent
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The actual native ambient point defined by a degree-one form of value one. -/
def ambientPointKoszul_nativeEvaluationPoint
    (v : Fin 4 → K) (f : homogeneousSubmodule (Fin 4) K 1)
    (hf : eval₂Hom (RingHom.id K) v f.val = 1) : Spec (.of K) ⟶ Proj PS :=
  Spec.map (CommRingCat.ofHom (AllCharacteristics.GradedChart.liftCoordinateOne PS f.val
    (eval₂Hom (RingHom.id K) v) hf)) ≫
      Proj.awayι PS f.val f.property (by decide : 0 < 1)

set_option backward.isDefEq.respectTransparency false in
private theorem nativeEvaluation_product_chart
    (v : Fin 4 → K) (f g : homogeneousSubmodule (Fin 4) K 1)
    (hf : eval₂Hom (RingHom.id K) v f.val = 1)
    (hg : eval₂Hom (RingHom.id K) v g.val = 1) :
    (AllCharacteristics.GradedChart.liftCoordinateOne PS (f.val * g.val)
        (eval₂Hom (RingHom.id K) v) (by rw [map_mul, hf, hg, mul_one])).comp
          (awayMap PS g.property rfl) =
      AllCharacteristics.GradedChart.liftCoordinateOne PS f.val
        (eval₂Hom (RingHom.id K) v) hf := by
  apply RingHom.ext
  intro z
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective PS f.property z
  rw [RingHom.comp_apply, awayMap_mk,
    AllCharacteristics.GradedChart.liftCoordinateOne_mk,
    AllCharacteristics.GradedChart.liftCoordinateOne_mk,
    map_mul, map_pow, hg, one_pow, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- Actual native projective evaluation at the same vector agrees for
every pair of degree-one normalizing forms of value one. -/
theorem ambientPointKoszul_nativeEvaluationPoint_eq
    (v : Fin 4 → K) (f g : homogeneousSubmodule (Fin 4) K 1)
    (hf : eval₂Hom (RingHom.id K) v f.val = 1)
    (hg : eval₂Hom (RingHom.id K) v g.val = 1) :
    ambientPointKoszul_nativeEvaluationPoint v f hf =
      ambientPointKoszul_nativeEvaluationPoint v g hg := by
  let e := eval₂Hom (RingHom.id K) v
  let q := AllCharacteristics.GradedChart.liftCoordinateOne PS (f.val * g.val) e
    (by rw [map_mul, hf, hg, mul_one])
  have hqf : q.comp (awayMap PS g.property rfl) =
      AllCharacteristics.GradedChart.liftCoordinateOne PS f.val e hf :=
    nativeEvaluation_product_chart v f g hf hg
  have hqg : q.comp (awayMap PS f.property (mul_comm f.val g.val)) =
      AllCharacteristics.GradedChart.liftCoordinateOne PS g.val e hg := by
    apply RingHom.ext
    intro z
    obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective PS g.property z
    dsimp only [q, e]
    rw [RingHom.comp_apply, awayMap_mk,
      AllCharacteristics.GradedChart.liftCoordinateOne_mk,
      AllCharacteristics.GradedChart.liftCoordinateOne_mk,
      map_mul, map_pow, hf, one_pow, mul_one]
  calc
    ambientPointKoszul_nativeEvaluationPoint v f hf =
        Spec.map (CommRingCat.ofHom q) ≫
          Proj.awayι PS (f.val * g.val) (SetLike.mul_mem_graded f.property g.property)
            (by decide : 0 < 1 + 1) := by
      unfold ambientPointKoszul_nativeEvaluationPoint
      rw [← hqf]
      change Spec.map (CommRingCat.ofHom (awayMap PS g.property rfl) ≫
        CommRingCat.ofHom q) ≫ _ = _
      rw [Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]
    _ = ambientPointKoszul_nativeEvaluationPoint v g hg := by
      unfold ambientPointKoszul_nativeEvaluationPoint
      rw [← hqg]
      change _ = Spec.map (CommRingCat.ofHom (awayMap PS f.property (mul_comm f.val g.val)) ≫
        CommRingCat.ofHom q) ≫ _
      rw [Spec.map_comp, Category.assoc, Proj.SpecMap_awayMap_awayι]

set_option backward.isDefEq.respectTransparency false in
/-- Centering a vector by an invertible basis gives its original native
evaluation point in every normalized standard coordinate chart. -/
theorem ambientPointKoszul_basisPoint_eq_nativeEvaluationPoint
    (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det) (v : Fin 4 → K)
    (hMv : M.mulVec v = ambientPointKoszul_vector K)
    (j : Fin 4) (hvj : v j = 1) :
    ambientPointKoszul_basisPoint M hM =
      ambientPointKoszul_nativeEvaluationPoint v ⟨X j, isHomogeneous_X K j⟩
        ((eval₂Hom_X' _ _ j).trans hvj) := by
  exact (ambientPointKoszul_basisPoint_eq_evaluation M hM v hMv).trans
    (ambientPointKoszul_nativeEvaluationPoint_eq v (ambientPointKoszul_basis M 0)
      ⟨X j, isHomogeneous_X K j⟩ (ambientPointKoszul_basis_eval_zero_one M v hMv)
      ((eval₂Hom_X' _ _ j).trans hvj))

end PfaffianDescent
