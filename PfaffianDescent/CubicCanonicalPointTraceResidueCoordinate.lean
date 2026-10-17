import PfaffianDescent.CubicCanonicalPointExtCoordinate
import PfaffianDescent.CubicCanonicalPointTraceAddHom

/-! # The actual canonical point trace in a constructed residue-field coordinate

The point Ext coordinate is constructed from smooth cubic geometry. The resulting
additive functional uses the actual closed-point pullback and actual surface trace.
Neither nonvanishing nor compatibility with the ground-field action is an input
to this construction. Ground-field linearity is proved in
`CubicCanonicalPointResidueTraceLinear`; global nonvanishing remains open.
-/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The actual canonical closed-point trace, written in the constructed residue
coordinate. No nonzero or trace-normalization premise is used. -/
def cubicCanonicalPointResidueTraceAddHom
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))] :
    L →+ K :=
  (@cubicCanonicalPointTraceAddHom K _ p hp hp0 hDomain L _ i hClosed hExtAmbient hExt).comp
    (@cubicCanonicalPointExtTwoCoordinate K _ p hp hp0 hSmooth L _ i hClosed
      hExt hExtStalk).symm.toAddMonoidHom

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation in the constructed coordinate recovers the actual geometric point
pullback trace of every point Ext class. -/
theorem cubicCanonicalPointResidueTrace_evaluate_class
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [hDomain : IsDomain (CoordinateRing (equationIdeal p hp))]
    [hSmooth : Smooth (hypersurfaceToBase p hp)] {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [hClosed : IsClosedImmersion i]
    [hExtAmbient : HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    [hExtStalk : HasExt.{u + 1} (ModuleCat ((Proj (grading (equationIdeal p hp))).presheaf.stalk (i default)))]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2) :
    @cubicCanonicalPointResidueTraceAddHom K _ p hp hp0 hDomain hSmooth L _ i hClosed
      hExtAmbient hExt hExtStalk
      (@cubicCanonicalPointExtTwoCoordinate K _ p hp hp0 hSmooth L _ i hClosed hExt hExtStalk z) =
      @cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K _ p hp hp0 hDomain hExtAmbient hExt
        ((Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules)
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
          (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp z (zero_add 2)) := by
  let e := @cubicCanonicalPointExtTwoCoordinate K _ p hp hp0 hSmooth L _ i hClosed hExt hExtStalk
  let tr := @cubicCanonicalPointTraceAddHom K _ p hp hp0 hDomain L _ i hClosed hExtAmbient hExt
  change tr (e.symm (e z)) = _
  exact (congrArg tr (e.symm_apply_apply z)).trans
    (@cubicCanonicalPointTraceAddHom_apply K _ p hp hp0 hDomain L _ i hClosed hExtAmbient hExt z)

end PfaffianDescent.ProjectiveNegativeTwist
