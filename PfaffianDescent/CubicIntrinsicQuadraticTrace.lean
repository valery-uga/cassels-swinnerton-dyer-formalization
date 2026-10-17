import PfaffianDescent.CubicIntrinsicMultiplicationNaturality
import PfaffianDescent.CubicQuadraticCanonicalTrace

/-! # Native intrinsic cubic duality is trace after actual multiplication -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

theorem cubicIntrinsicNegativeThree_dual_apply_pushforward
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (z : schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
      (sheafOfModules (grading (equationIdeal p hp)) 3) 2) :
    cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0 z =
      cubicPushforwardNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0
        (cubicIntrinsicCohomologyTwoEquivPushforward K p hp hp0 3 z) := rfl

theorem cubicIntrinsicNegativeOne_trace_apply_pushforward
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (z : schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2) :
    cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0 z =
      cubicPushforwardNegativeOneCohomologyTwoTraceEquiv K p hp hp0
        (cubicIntrinsicCohomologyTwoEquivPushforward K p hp hp0 1 z) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual native intrinsic quadratic pairing equals the actual
canonical scalar trace after multiplication by the restricted quadratic.
No comparison naturality or trace-normalization hypothesis is supplied. -/
theorem cubicIntrinsicNegativeThree_pairing_eq_canonical_trace_multiplication
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (z : schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
      (sheafOfModules (grading (equationIdeal p hp)) 3) 2)
    (q : homogeneousSubmodule (Fin 4) K 2) :
    cubicIntrinsicNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0 z q =
      cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0
        (z.comp (Ext.mk₀ (mulHomogeneous (grading (equationIdeal p hp))
          (cubicQuadraticRestriction K p hp q) 1)) (add_zero 2)) := by
  rw [cubicIntrinsicNegativeThree_dual_apply_pushforward,
    cubicIntrinsicNegativeOne_trace_apply_pushforward]
  exact (cubicPushforwardNegativeThree_pairing_eq_canonical_trace_multiplication K p hp hp0 _ q).trans
    (congrArg (cubicPushforwardNegativeOneCohomologyTwoTraceEquiv K p hp hp0)
      (cubicIntrinsicCohomologyTwoEquivPushforward_mulHomogeneous K p hp hp0
        1 2 (cubicQuadraticRestriction K p hp q) z).symm)

end PfaffianDescent.ProjectiveNegativeTwist
