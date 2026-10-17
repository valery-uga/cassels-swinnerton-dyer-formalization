import PfaffianDescent.CubicCanonicalTraceScalarDiagram
import PfaffianDescent.CubicIntrinsicQuadraticTrace

/-! # Scalar compatibility of the actual intrinsic cubic canonical trace -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic canonical trace scales by the ground-field scalar under
the ACTUAL surface coefficient morphism. -/
theorem cubicIntrinsicCanonicalTrace_scalar_multiplication
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (c : K) (z : schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2) :
    cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0
        (z.comp (Ext.mk₀ (mulHomogeneous (grading (equationIdeal p hp))
          (cubicScalarHomogeneous K p hp c) 1)) (add_zero 2)) =
      c * cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0 z := by
  rw [cubicIntrinsicNegativeOne_trace_apply_pushforward,
    cubicIntrinsicNegativeOne_trace_apply_pushforward]
  exact (congrArg (cubicPushforwardNegativeOneCohomologyTwoTraceEquiv K p hp hp0)
    (cubicIntrinsicCohomologyTwoEquivPushforward_mulHomogeneous K p hp hp0
      1 0 (cubicScalarHomogeneous K p hp c) z)).trans
    (cubicPushforwardCanonicalTrace_scalar_multiplication K p hp hp0 c _)

end PfaffianDescent.ProjectiveNegativeTwist
