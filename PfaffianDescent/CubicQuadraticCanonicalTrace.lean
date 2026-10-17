import PfaffianDescent.P3QuadraticIntrinsicTrace
import PfaffianDescent.CubicQuadraticRestrictionDiagram

/-! # The native cubic quadratic pairing as actual canonical trace -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

theorem cubicPushforwardNegativeThree_dual_apply_connecting
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    (z : schemeModuleCohomology (Proj PS) (cubicPushforwardTwist K p hp 3) 2) :
    cubicPushforwardNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0 z =
      p3NegativeSixCohomologyThreeDualQuadraticEquiv K
        (cubicPushforwardNegativeThreeCohomologyTwoEquivAmbientNegativeSixThree K p hp hp0 z) := rfl

theorem cubicPushforwardNegativeOne_trace_apply_connecting
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    (z : schemeModuleCohomology (Proj PS) (cubicPushforwardTwist K p hp 1) 2) :
    cubicPushforwardNegativeOneCohomologyTwoTraceEquiv K p hp hp0 z =
      p3NegativeFourCohomologyThreeTraceEquiv K
        (cubicPushforwardNegativeOneCohomologyTwoEquivAmbientNegativeFourThree K p hp hp0 z) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The native quadratic pairing equals the canonical cubic trace after
the actual pushforward of surface multiplication. Both connecting maps
and the coefficient diagram are internally constructed. -/
theorem cubicPushforwardNegativeThree_pairing_eq_canonical_trace_multiplication
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    (z : schemeModuleCohomology (Proj PS) (cubicPushforwardTwist K p hp 3) 2)
    (q : homogeneousSubmodule (Fin 4) K 2) :
    cubicPushforwardNegativeThreeCohomologyTwoEquivDualQuadratic K p hp hp0 z q =
      cubicPushforwardNegativeOneCohomologyTwoTraceEquiv K p hp hp0
        (z.comp (Ext.mk₀ (cubicQuadraticRestrictionDiagram K p hp q).τ₃) (add_zero 2)) := by
  rw [cubicPushforwardNegativeThree_dual_apply_connecting,
    cubicPushforwardNegativeOne_trace_apply_connecting]
  exact (p3NegativeSixCohomologyThreeDualQuadraticEquiv_eq_trace_multiplication K _ q).trans
    (congrArg (p3NegativeFourCohomologyThreeTraceEquiv K)
      (cubicQuadraticRestriction_connecting_naturality K p hp hp0 q z).symm)

end PfaffianDescent.ProjectiveNegativeTwist
