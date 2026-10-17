import PfaffianDescent.CubicCanonicalCohomologyTrace

/-! # An opaque additive-map interface to the actual intrinsic canonical trace -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- The existing actual canonical trace, with its additive-map interface
constructed without any point-specific geometric instances. -/
def cubicIntrinsicCanonicalTraceAddHom
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules] :
    schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2 →+ K :=
  (cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0).toAddMonoidHom

theorem cubicIntrinsicCanonicalTraceAddHom_apply
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (z : schemeModuleCohomology (Proj (grading (equationIdeal p hp)))
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2) :
    cubicIntrinsicCanonicalTraceAddHom K p hp hp0 z =
      cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0 z := rfl

end PfaffianDescent.ProjectiveNegativeTwist
