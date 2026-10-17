import PfaffianDescent.ActualIdealUniversalDifferentialPushforward
import PfaffianDescent.ActualClosedPointConormalNativeTensorFiber

/- SOURCE ONLY / UNVERIFIED. Genuine GLOBAL conormal→relative Omega map.
Actual ideal quotient kills the Leibniz extra term, so the actual universal
D factors by the true pullback adjunction. No local map identification assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [CommRing K] {X Z : Scheme.{u}}

lemma actualClosedImmersionIdealToUnit_quotient_zero
    (q : Z ⟶ X) [IsClosedImmersion q] :
    closedImmersionModuleToUnit q ≫ closedImmersionUnitToPushforwardUnit q = 0 := by
  have hkernel : closedImmersionKernelModuleToUnit q ≫
      closedImmersionUnitToPushforwardUnit q = 0 := by
    change kernel.ι (closedImmersionUnitToPushforwardUnit q) ≫
      closedImmersionUnitToPushforwardUnit q = 0
    exact kernel.condition _
  calc
    _ = (closedImmersionModuleToKernel q ≫ closedImmersionKernelModuleToUnit q) ≫
        closedImmersionUnitToPushforwardUnit q :=
      congrArg (fun a => a ≫ closedImmersionUnitToPushforwardUnit q)
        (closedImmersionModuleToKernel_comp q).symm
    _ = closedImmersionModuleToKernel q ≫
        (closedImmersionKernelModuleToUnit q ≫ closedImmersionUnitToPushforwardUnit q) :=
      Category.assoc _ _ _
    _ = closedImmersionModuleToKernel q ≫ 0 :=
      congrArg (fun a => closedImmersionModuleToKernel q ≫ a) hkernel
    _ = 0 := comp_zero

def actualClosedImmersionIdealUniversalDifferentialPushforward
    (g : X ⟶ Spec (.of K)) (q : Z ⟶ X) [IsClosedImmersion q] :
    closedImmersionModule q ⟶
      (Scheme.Modules.pushforward q).obj
        ((Scheme.Modules.pullback q).obj (schemeRelativeDifferentials g)) :=
  actualIdealUniversalDifferentialPushforward g q (closedImmersionModule q)
    (closedImmersionModuleToUnit q) (actualClosedImmersionIdealToUnit_quotient_zero q)

def actualGlobalClosedConormalDifferentialMap
    (g : X ⟶ Spec (.of K)) (q : Z ⟶ X) [IsClosedImmersion q] :
    actualClosedImmersionConormalModule q ⟶
      (Scheme.Modules.pullback q).obj (schemeRelativeDifferentials g) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _).symm
    (actualClosedImmersionIdealUniversalDifferentialPushforward g q)

lemma actualGlobalClosedConormalDifferentialMap_adjunct
    (g : X ⟶ Spec (.of K)) (q : Z ⟶ X) [IsClosedImmersion q] :
    ((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _)
      (actualGlobalClosedConormalDifferentialMap g q) =
      actualClosedImmersionIdealUniversalDifferentialPushforward g q :=
  Equiv.apply_symm_apply _ _

lemma actualGlobalClosedConormalDifferentialMap_adjunct_section
    (g : X ⟶ Spec (.of K)) (q : Z ⟶ X) [IsClosedImmersion q]
    (U : X.Opens) (z : (closedImmersionModule q).val.obj (op U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction q).homEquiv _ _)
      (actualGlobalClosedConormalDifferentialMap g q)).val.app (op U) z =
    ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
      (schemeRelativeDifferentials g)).val.app (op U)
      (actualRelativeDifferentialSection g U
        ((closedImmersionModuleToUnit q).val.app (op U) z)) := by
  rw [actualGlobalClosedConormalDifferentialMap_adjunct]
  rfl

end PfaffianDescent
