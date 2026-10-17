import PfaffianDescent.CubicCanonicalPointTraceAddHom
import PfaffianDescent.CubicIntrinsicCanonicalTraceScalar

/-! # Scalar compatibility of the entire actual canonical point trace -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

set_option backward.isDefEq.respectTransparency false in
/-- The actual canonical point trace scales under actual cubic coefficient
multiplication for every point Ext class, independently of a chosen Koszul
representative or affine chart. -/
theorem cubicCanonicalPointTraceAddHom_postcomp_scalar
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [IsDomain (CoordinateRing (equationIdeal p hp))]
    {L : Type u} [Field L]
    (i : Spec (.of L) ⟶ Proj (grading (equationIdeal p hp))) [IsClosedImmersion i]
    [HasExt.{u} (Proj PS).Modules]
    [hExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules]
    (c : K)
    (z : Ext.{u} (closedImmersionIdealTwistSequence i
      (SheafOfModules.unit (Proj (grading (equationIdeal p hp))).ringCatSheaf)).X₃
      (sheafOfModules (grading (equationIdeal p hp)) 1) 2) :
    cubicCanonicalPointTraceAddHom K p hp hp0 i
        (z.comp (Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules)
          (mulHomogeneous (grading (equationIdeal p hp))
            (cubicScalarHomogeneous K p hp c) 1)) (add_zero 2)) =
      c * cubicCanonicalPointTraceAddHom K p hp hp0 i z := by
  letI : HasExt.{u} (SheafOfModules.{u} (Proj (grading (equationIdeal p hp))).ringCatSheaf) := hExt
  let g := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
    (closedImmersionIdealTwistSequenceUnitTargetIso i).inv
  let phi := mulHomogeneous (grading (equationIdeal p hp))
    (cubicScalarHomogeneous K p hp c) 1
  rw [cubicCanonicalPointTraceAddHom_apply, cubicCanonicalPointTraceAddHom_apply]
  exact (congrArg (cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0)
    (extPullback_postcomp.{u + 1, u, u}
      (C := (Proj (grading (equationIdeal p hp))).Modules)
      (n := 2) g z phi).symm).trans
      (cubicIntrinsicCanonicalTrace_scalar_multiplication K p hp hp0 c
        ((Ext.mk₀ (C := (Proj (grading (equationIdeal p hp))).Modules) g).comp z
          (zero_add 2)))

end PfaffianDescent.ProjectiveNegativeTwist
