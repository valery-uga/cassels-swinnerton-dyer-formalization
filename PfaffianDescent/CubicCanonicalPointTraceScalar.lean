import PfaffianDescent.CubicIntrinsicCanonicalTraceScalar
import PfaffianDescent.FieldPointKoszulCoefficientNaturality
import PfaffianDescent.CanonicalQuotientStalkCoordinate

/-! # Scalar compatibility of the actual canonical point trace functional -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Opposite MvPolynomial AllCharacteristics.HomogeneousProjective
open scoped nonZeroDivisors
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentCechExact LaurentLocalization
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K
local notation "CS" => Proj (grading (equationIdeal p hp))

set_option backward.isDefEq.respectTransparency false in
/-- The actual canonical scalar trace of a canonical point Koszul class
scales by a ground-field scalar when its coefficient is multiplied by the
actual scalar section. This proves the geometric scalar compatibility. -/
theorem cubicCanonicalPoint_trace_scalar_multiplication
    (hp0 : p ≠ 0) [IsDomain (CoordinateRing (equationIdeal p hp))]
    [HasExt.{u} (Proj PS).Modules] [hExt : HasExt.{u} (CS).Modules]
    {L : Type u} [Field L] (i : Spec (.of L) ⟶ CS) [IsClosedImmersion i]
    [IsAffineHom (pullback.diagonal (terminal.from CS))]
    {J : Type u} (V : J → (CS).Opens)
    (hV : (Opens.grothendieckTopology CS).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor (CS).ringCatSheaf (V j)).obj
      (SheafOfModules.unit (CS).ringCatSheaf) ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver (CS).sheaf (V j))))
    (U : (CS).Opens) (hU : IsAffineOpen U) (hx : i default ∈ U) (q f : Γ(CS, U))
    (hqmax : (CS).presheaf.germ U (i default) hx q ∈ IsLocalRing.maximalIdeal
      ((CS).presheaf.stalk (i default)))
    (hfmax : (CS).presheaf.germ U (i default) hx f ∈ IsLocalRing.maximalIdeal
      ((CS).presheaf.stalk (i default)))
    (haway : ∀ (z : CS) (hz : z ∈ U), z ≠ i default →
      Ideal.span ({(CS).presheaf.germ U z hz q, (CS).presheaf.germ U z hz f} :
        Set ((CS).presheaf.stalk z)) = ⊤)
    (hqreg : (CS).presheaf.germ U (i default) hx q ∈ ((CS).presheaf.stalk (i default))⁰)
    (hfreg : Ideal.Quotient.mk (Ideal.span {(CS).presheaf.germ U (i default) hx q})
      ((CS).presheaf.germ U (i default) hx f) ∈
      (((CS).presheaf.stalk (i default)) ⧸
        Ideal.span {(CS).presheaf.germ U (i default) hx q})⁰)
    (y : (sheafOfModules (grading (equationIdeal p hp)) 1).val.obj (op U)) :
    letI := schemeModuleStalkModule (show (CS).Modules from
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
      (i default)
    ∀ (hkernel : LinearMap.ker (closedImmersionPushforwardStalkFromRingLinearMap
      i (i default)) = Ideal.span ({(CS).presheaf.germ U (i default) hx q,
        (CS).presheaf.germ U (i default) hx f} : Set _)),
    let qM := closedImmersionUnitTwistStalkQuotientIso i (i default)
      ((CS).presheaf.germ U (i default) hx q) ((CS).presheaf.germ U (i default) hx f) hkernel
    ∀ c : K,
      cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0
        ((Ext.mk₀ (C := (CS).Modules)
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
            (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp
          (fieldPointSectionRepresenterKoszulDegreeTwoClass i (SheafOfModules.unit (CS).ringCatSheaf)
            V hV eV U hx q f qM haway hqreg hfreg
            (sheafOfModules (grading (equationIdeal p hp)) 1)
            ((mulHomogeneous (grading (equationIdeal p hp)) (cubicScalarHomogeneous K p hp c) 1).val.app
              (op U) y)) (zero_add 2)) =
      c * cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0
        ((Ext.mk₀ (C := (CS).Modules)
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
            (closedImmersionIdealTwistSequenceUnitTargetIso i).inv)).comp
          (fieldPointSectionRepresenterKoszulDegreeTwoClass i (SheafOfModules.unit (CS).ringCatSheaf)
            V hV eV U hx q f qM haway hqreg hfreg
            (sheafOfModules (grading (equationIdeal p hp)) 1) y) (zero_add 2)) := by
  dsimp only
  letI := schemeModuleStalkModule (show (CS).Modules from
    (Scheme.Modules.pushforward i).obj (SheafOfModules.unit (Spec (.of L)).ringCatSheaf))
    (i default)
  letI : HasExt.{u} (SheafOfModules.{u} (CS).ringCatSheaf) := hExt
  intro hkernel c
  let qM := closedImmersionUnitTwistStalkQuotientIso i (i default)
    ((CS).presheaf.germ U (i default) hx q) ((CS).presheaf.germ U (i default) hx f) hkernel
  let g := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i ≫
    (closedImmersionIdealTwistSequenceUnitTargetIso i).inv
  let a := fieldPointSectionRepresenterKoszulDegreeTwoClass i (SheafOfModules.unit (CS).ringCatSheaf)
    V hV eV U hx q f qM haway hqreg hfreg
    (sheafOfModules (grading (equationIdeal p hp)) 1) y
  let hmul := mulHomogeneous (grading (equationIdeal p hp)) (cubicScalarHomogeneous K p hp c) 1
  have hcoef := fieldPointSectionRepresenterKoszulDegreeTwoClass_postcomp i
    (SheafOfModules.unit (CS).ringCatSheaf) V hV eV U hx q f qM haway hqreg hfreg
    (sheafOfModules (grading (equationIdeal p hp)) 1)
    (sheafOfModules (grading (equationIdeal p hp)) 1) y hmul
  have hpull : ((Ext.mk₀ g).comp a (zero_add 2)).comp (Ext.mk₀ hmul) (add_zero 2) =
      (Ext.mk₀ g).comp
        (fieldPointSectionRepresenterKoszulDegreeTwoClass i (SheafOfModules.unit (CS).ringCatSheaf)
          V hV eV U hx q f qM haway hqreg hfreg
          (sheafOfModules (grading (equationIdeal p hp)) 1) (hmul.val.app (op U) y))
        (zero_add 2) := by
    exact (extPullback_postcomp g a hmul).trans
      (congrArg (fun t => (Ext.mk₀ g).comp t (zero_add 2)) hcoef)
  exact (congrArg (cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K p hp hp0) hpull.symm).trans
    (cubicIntrinsicCanonicalTrace_scalar_multiplication K p hp hp0 c
      ((Ext.mk₀ g).comp a (zero_add 2)))

end PfaffianDescent.ProjectiveNegativeTwist
