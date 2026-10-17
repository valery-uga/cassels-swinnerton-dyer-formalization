import PfaffianDescent.CubicIntrinsicCanonicalTraceAddHom
import PfaffianDescent.SchemePushforwardUnitSections
import PfaffianDescent.ExtPullbackTraceCoordinate

/-! # The actual canonical trace after closed-point pullback

This interface constructs the trace before introducing smoothness or a stalk
Ext coordinate. It uses the actual closed immersion and intrinsic surface trace.
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
/-- The additive trace of an actual point Ext class, with no local coordinate
or nonvanishing premise. -/
def cubicCanonicalPointTraceAddHom
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [IsClosedImmersion i]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules] :
    Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2 →+ K := by
  refine {
    toFun := fun z =>
      cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0
      ((Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
          (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp z (zero_add 2))
    map_zero' := ?_
    map_add' := ?_ }
  · rw [Ext.comp_zero, map_zero]
  · intro z w
    rw [Ext.comp_add, map_add]

set_option backward.isDefEq.respectTransparency false in
theorem cubicCanonicalPointTraceAddHom_apply
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [IsClosedImmersion i]
    [HasExt.{u} (Proj PS).Modules]
    [HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2) :
    cubicCanonicalPointTraceAddHom K p hp hp0 i z =
      cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0
        ((Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules)
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
          (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp z (zero_add 2)) :=
  rfl

end PfaffianDescent.ProjectiveNegativeTwist
