import PfaffianDescent.ActualModuleLocalTensorRightUnitAction
import PfaffianDescent.SchemeModuleInternalHomUnitMap
import PfaffianDescent.SchemeModuleInternalHomEvaluation

/-! SOURCE ONLY / UNVERIFIED. Actual tensor insertion, symmetry and
original-inclusion evaluation. No local comparison is a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open scoped TensorProduct
universe u
variable {X : Scheme.{u}}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma actualModuleLocalTensorRightUnitInverse185
    (M : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) :
    (schemeModuleTensorUnitRightIso M).inv.val.app (op U) m =
      actualModuleLocalTensorSection M (SheafOfModules.unit X.ringCatSheaf) U m (1 : Γ(X, U)) := by
  let e := schemeModuleTensorUnitRightIso M
  let s := actualModuleLocalTensorSection M (SheafOfModules.unit X.ringCatSheaf) U m (1 : Γ(X, U))
  have hv : e.hom.val.app (op U) s = m :=
    (actualModuleLocalTensorRightUnitAction M U m (1 : Γ(X, U))).trans (one_smul _ _)
  have hc : e.inv.val.app (op U) (e.hom.val.app (op U) s) = s := by
    have h := ConcreteCategory.congr_hom
      (congrArg (fun f : schemeModuleTensor M (SheafOfModules.unit X.ringCatSheaf) ⟶
          schemeModuleTensor M (SheafOfModules.unit X.ringCatSheaf) => f.val.app (op U))
        e.hom_inv_id) s
    exact h
  exact (congrArg (e.inv.val.app (op U)) hv).symm.trans hc

lemma actualModuleLocalTensorRightUnitInsert185
    (M N : X.Modules) (f : SheafOfModules.unit X.ringCatSheaf ⟶ N)
    (U : X.Opens) (m : M.val.obj (op U)) :
    ((schemeModuleTensorUnitRightIso M).inv ≫ schemeModuleTensorMap (𝟙 M) f).val.app
        (op U) m =
      actualModuleLocalTensorSection M N U m (f.val.app (op U) (1 : Γ(X, U))) := by
  change (schemeModuleTensorMap (𝟙 M) f).val.app (op U)
    ((schemeModuleTensorUnitRightIso M).inv.val.app (op U) m) = _
  rw [actualModuleLocalTensorRightUnitInverse185]
  exact actualModuleLocalTensorSection_naturality (𝟙 M) f U m (1 : Γ(X, U))

lemma actualModuleLocalTensorSymmetry185
    (M N : X.Modules) (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (schemeModuleTensorSymmetry M N).hom.val.app (op U)
      (actualModuleLocalTensorSection M N U m n) =
        actualModuleLocalTensorSection N M U n m := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  letI : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.symmetricCategory
  let b := (β_ M.val N.val).hom
  have hn := congrArg (fun v => v.app (op U) (m ⊗ₜ[Γ(X, U)] n))
    (adj.unit.naturality b)
  have hb : b.app (op U) (m ⊗ₜ[Γ(X, U)] n) = n ⊗ₜ[Γ(X, U)] m := by
    rfl
  exact hn.symm.trans (congrArg ((adj.unit.app _).app (op U)) hb)

lemma actualDualEvaluation_unitToHom_one185
    (I : X.Modules) (j : I ⟶ SheafOfModules.unit X.ringCatSheaf)
    (U : X.Opens) (i : I.val.obj (op U)) :
    (SchemeModuleInternalHom.dualEvaluation I).val.app (op U)
      (actualModuleLocalTensorSection I (SchemeModuleInternalHom.dual I) U i
        ((SchemeModuleInternalHom.unitToHom j).val.app (op U) (1 : Γ(X, U)))) =
      j.val.app (op U) i := by
  let d := (SchemeModuleInternalHom.unitToHom j).val.app (op U) (1 : Γ(X, U))
  have he := congrArg (fun v => v.app (op U) (i ⊗ₜ[Γ(X, U)] d))
    (SchemeModuleInternalHom.evaluation_raw I (SheafOfModules.unit X.ringCatSheaf))
  change (SchemeModuleInternalHom.dualEvaluation I).val.app (op U)
    (actualModuleLocalTensorSection I (SchemeModuleInternalHom.dual I) U i d) =
      d.1.app (op (Over.mk (𝟙 U))) i at he
  have hd : d = SchemeModuleInternalHom.homSection j U :=
    SchemeModuleInternalHom.unitToHom_one j U
  exact he.trans ((congrArg (fun a : (SchemeModuleInternalHom.dual I).val.obj (op U) =>
      a.1.app (op (Over.mk (𝟙 U))) i) hd).trans
    (SchemeModuleInternalHom.homSection_apply j U (Over.mk (𝟙 U)) i))

end PfaffianDescent
