import PfaffianDescent.ActualPointLocalAdjunctionSectionEvaluation
import PfaffianDescent.ActualGlobalClosedConormalDifferentialMap

/- SOURCE ONLY / UNVERIFIED. The genuinely GLOBAL conormal map acts
on LOCAL original ideal sections by the actual universal D at that open,
using the true original-point adjoint, without global-generation assumptions. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite IdealSheafDataModule
universe u

lemma actualGlobalConormalPointLocalSectionAction
    {k L : Type u} [CommRing k] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) (q : Spec (.of L) ⟶ X) [IsClosedImmersion q]
    (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤)
    (z : (closedImmersionModule q).val.obj (op U)) :
    (moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap g q)
      (actualPointLocalSectionClass q (closedImmersionModule q) U hU z) =
    actualPointLocalSectionClass q (schemeRelativeDifferentials g) U hU
      (actualRelativeDifferentialSection g U
        ((closedImmersionModuleToUnit q).val.app (op U) z)) := by
  have h := actualPointLocalAdjunctionSectionEvaluation q
    (show X.Modules from closedImmersionModule q)
    ((Scheme.Modules.pullback q).obj (schemeRelativeDifferentials g))
    U hU z (actualGlobalClosedConormalDifferentialMap g q)
  exact h.trans (congrArg
    (fun t => ((Scheme.Modules.pullback q).obj (schemeRelativeDifferentials g)).val.map
      (eqToHom (congrArg op hU)) t)
    (actualGlobalClosedConormalDifferentialMap_adjunct_section g q U z))

lemma actualGlobalConormalPointLocalSectionAction_of_factor
    {k L : Type u} [CommRing k] [Field L] {X Y : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) (f : Y ⟶ X) [IsOpenImmersion f]
    (j : Spec (.of L) ⟶ Y) (q : Spec (.of L) ⟶ X) [IsClosedImmersion q]
    (hfac : j ≫ f = q)
    (z : (closedImmersionModule q).val.obj (op (f ''ᵁ (⊤ : Y.Opens)))) :
    (moduleSpecΓFunctor (R := .of L)).map
      (actualGlobalClosedConormalDifferentialMap g q)
      (actualPointLocalSectionClass q (closedImmersionModule q) (f ''ᵁ ⊤)
        (actualFieldPointFactor_preimage_image_top f j q hfac) z) =
    actualPointLocalSectionClass q (schemeRelativeDifferentials g) (f ''ᵁ ⊤)
      (actualFieldPointFactor_preimage_image_top f j q hfac)
      (actualRelativeDifferentialSection g (f ''ᵁ ⊤)
        ((closedImmersionModuleToUnit q).val.app (op (f ''ᵁ ⊤)) z)) :=
  actualGlobalConormalPointLocalSectionAction g q (f ''ᵁ ⊤)
    (actualFieldPointFactor_preimage_image_top f j q hfac) z

end PfaffianDescent
