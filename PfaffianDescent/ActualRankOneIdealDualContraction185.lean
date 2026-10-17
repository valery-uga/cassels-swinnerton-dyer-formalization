import PfaffianDescent.ActualLocalTensorDualInsertion185
import PfaffianDescent.ActualModuleLocalTensorInverseContraction
import PfaffianDescent.SchemeModuleRankOneDualKernelIso
import PfaffianDescent.SchemeModuleInternalHomRankOneTargetEvaluation

/-! SOURCE ONLY / UNVERIFIED. The actual rank-one ideal constructs its
own evaluation isomorphism and sheafification comparison. The derived
contraction acts by the SAME original inclusion j. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def schemeModuleRankOneOriginalDualPairingIso185
    (I : X.Modules) (hI : schemeModuleLocallyRankOne I) :
    schemeModuleTensor I (SchemeModuleInternalHom.dual I) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI : IsIso (SchemeModuleInternalHom.dualEvaluation I) :=
    SchemeModuleInternalHom.evaluation_isIso_of_locallyRankOne I
      (SheafOfModules.unit X.ringCatSheaf) hI
  exact asIso (SchemeModuleInternalHom.dualEvaluation I)

def schemeModuleRankOneOriginalDualContraction185
    (I M : X.Modules) (hI : schemeModuleLocallyRankOne I) :
    schemeModuleTensor (schemeModuleTensor M I) (SchemeModuleInternalHom.dual I) ⟶ M := by
  letI := schemeModuleLocallyRankOne_rightComparison_isIso
    (PresheafOfModules.Monoidal.tensorObj M.val I.val) (SchemeModuleInternalHom.dual I)
      (schemeModuleLocallyRankOne_dual I hI)
  exact schemeModuleTensorContraction M I (SchemeModuleInternalHom.dual I)
    (schemeModuleRankOneOriginalDualPairingIso185 I hI)

lemma actualRankOneOriginalDualContraction_inclusion185
    (I M : X.Modules) (hI : schemeModuleLocallyRankOne I)
    (j : I ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (m : M.val.obj (op U)) (i : I.val.obj (op U)) :
    (schemeModuleRankOneOriginalDualContraction185 I M hI).val.app (op U)
      (actualModuleLocalTensorSection (schemeModuleTensor M I)
        (SchemeModuleInternalHom.dual I) U
        (actualModuleLocalTensorSection M I U m i)
        ((SchemeModuleInternalHom.unitToHom j).val.app (op U) (1 : Γ(X, U)))) =
      (j.val.app (op U) i) • m := by
  let D := SchemeModuleInternalHom.dual I
  letI := schemeModuleLocallyRankOne_rightComparison_isIso
    (PresheafOfModules.Monoidal.tensorObj M.val I.val) D
      (schemeModuleLocallyRankOne_dual I hI)
  have hc := actualModuleLocalTensorInverseContraction M I D
    (schemeModuleRankOneOriginalDualPairingIso185 I hI) U m i
      ((SchemeModuleInternalHom.unitToHom j).val.app (op U) (1 : Γ(X, U)))
  change (schemeModuleRankOneOriginalDualContraction185 I M hI).val.app (op U)
    (actualModuleLocalTensorSection (schemeModuleTensor M I) D U
      (actualModuleLocalTensorSection M I U m i)
      ((SchemeModuleInternalHom.unitToHom j).val.app (op U) (1 : Γ(X, U)))) =
      ((SchemeModuleInternalHom.dualEvaluation I).val.app (op U)
        (actualModuleLocalTensorSection I D U i
          ((SchemeModuleInternalHom.unitToHom j).val.app (op U) (1 : Γ(X, U))))) • m at hc
  exact hc.trans (congrArg (fun c : Γ(X, U) => c • m)
    (actualDualEvaluation_unitToHom_one185 I j U i))

/-- Equality of actual sheaf morphisms, derived by the native adjunction
on the raw tensor source; no generation or action certificate is assumed. -/
theorem schemeModuleRankOneOriginalDualContraction_action185
    (I M : X.Modules) (hI : schemeModuleLocallyRankOne I)
    (j : I ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (schemeModuleTensorUnitRightIso (schemeModuleTensor M I)).inv ≫
      schemeModuleTensorMap (𝟙 (schemeModuleTensor M I))
        (SchemeModuleInternalHom.unitToHom j) ≫
      schemeModuleRankOneOriginalDualContraction185 I M hI =
    schemeModuleTensorMap (𝟙 M) j ≫ (schemeModuleTensorUnitRightIso M).hom := by
  let A := schemeModuleTensor M I
  let C := schemeModuleRankOneOriginalDualContraction185 I M hI
  let delta := SchemeModuleInternalHom.unitToHom j
  let l : A ⟶ M := (schemeModuleTensorUnitRightIso A).inv ≫
    schemeModuleTensorMap (𝟙 A) delta ≫ C
  let r : A ⟶ M := schemeModuleTensorMap (𝟙 M) j ≫
    (schemeModuleTensorUnitRightIso M).hom
  let raw := PresheafOfModules.Monoidal.tensorObj M.val I.val
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  change l = r
  apply (adj.homEquiv raw M).injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro m i
  change l.val.app U (actualModuleLocalTensorSection M I U.unop m i) =
    r.val.app U (actualModuleLocalTensorSection M I U.unop m i)
  have hi := actualModuleLocalTensorRightUnitInsert185 A
    (SchemeModuleInternalHom.dual I) delta U.unop
      (actualModuleLocalTensorSection M I U.unop m i)
  have hl : l.val.app U (actualModuleLocalTensorSection M I U.unop m i) =
      (j.val.app U i) • m := by
    change C.val.app U (((schemeModuleTensorUnitRightIso A).inv ≫
      schemeModuleTensorMap (𝟙 A) delta).val.app U
        (actualModuleLocalTensorSection M I U.unop m i)) = _
    exact (congrArg (fun z :
        (schemeModuleTensor A (SchemeModuleInternalHom.dual I)).val.obj
          (op U.unop) => C.val.app (op U.unop) z) hi).trans
      (actualRankOneOriginalDualContraction_inclusion185 I M hI j U.unop m i)
  have hr : r.val.app U (actualModuleLocalTensorSection M I U.unop m i) =
      (j.val.app U i) • m := by
    change (schemeModuleTensorUnitRightIso M).hom.val.app U
      ((schemeModuleTensorMap (𝟙 M) j).val.app U
        (actualModuleLocalTensorSection M I U.unop m i)) = _
    rw [actualModuleLocalTensorSection_naturality]
    exact actualModuleLocalTensorRightUnitAction M U.unop m (j.val.app U i)
  exact hl.trans hr.symm

end PfaffianDescent
