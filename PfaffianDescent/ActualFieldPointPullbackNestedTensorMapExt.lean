import PfaffianDescent.ActualFieldPointPullbackSheafificationMapExt
import PfaffianDescent.ActualPointLocalSectionClassNaturality
import PfaffianDescent.ActualModuleLocalTensorSection

/-! SOURCE ONLY / UNVERIFIED. The actual negative-factor sheafification
comparison and both actual adjunctions derive detection on triple LOCAL
pure tensors. No desired full-fiber map comparison is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualModuleSheafificationRightComparison_pureSection
    {X : Scheme.{u}} (M N T : X.Modules) (U : X.Opens)
    (w : M.val.obj (op U)) (n : N.val.obj (op U)) (t : T.val.obj (op U)) :
    let Q := PresheafOfModules.Monoidal.tensorObj M.val N.val
    let A := PresheafOfModules.Monoidal.tensorObj Q T.val
    let sa := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    (schemeModuleTensorSheafificationRightComparison Q T).val.app (op U)
      ((sa.unit.app A).app (op U)
        ((w ⊗ₜ[Γ(X, U)] n) ⊗ₜ[Γ(X, U)] t)) =
      actualModuleLocalTensorSection (schemeModuleTensor M N) T U
        (actualModuleLocalTensorSection M N U w n) t := by
  let Q := PresheafOfModules.Monoidal.tensorObj M.val N.val
  let A := PresheafOfModules.Monoidal.tensorObj Q T.val
  let sa := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let cr := PresheafOfModules.Monoidal.tensorHom (sa.unit.app Q) (𝟙 T.val)
  have hn := congrArg (fun v => v.app (op U)
    ((w ⊗ₜ[Γ(X, U)] n) ⊗ₜ[Γ(X, U)] t)) (sa.unit.naturality cr)
  exact hn.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem actualFieldPointPullbackNestedTensorMap_ext
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M N T : X.Modules)
    [IsIso (schemeModuleTensorSheafificationRightComparison
      (PresheafOfModules.Monoidal.tensorObj M.val N.val) T)]
    (V : (Spec (.of L)).Modules)
    (d₁ d₂ : (Scheme.Modules.pullback q).obj
      (schemeModuleTensor (schemeModuleTensor M N) T) ⟶ V)
    (h : ∀ (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤)
        (w : M.val.obj (op U)) (n : N.val.obj (op U)) (t : T.val.obj (op U)),
      (moduleSpecΓFunctor (R := .of L)).map d₁
        (actualPointLocalSectionClass q (schemeModuleTensor (schemeModuleTensor M N) T)
          U hU (actualModuleLocalTensorSection (schemeModuleTensor M N) T U
            (actualModuleLocalTensorSection M N U w n) t)) =
      (moduleSpecΓFunctor (R := .of L)).map d₂
        (actualPointLocalSectionClass q (schemeModuleTensor (schemeModuleTensor M N) T)
          U hU (actualModuleLocalTensorSection (schemeModuleTensor M N) T U
            (actualModuleLocalTensorSection M N U w n) t))) :
    d₁ = d₂ := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let sa := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let P := Scheme.Modules.pullback q
  let Q := PresheafOfModules.Monoidal.tensorObj M.val N.val
  let A := PresheafOfModules.Monoidal.tensorObj Q T.val
  let c := schemeModuleTensorSheafificationRightComparison Q T
  letI : IsIso (P.map c) := by infer_instance
  apply (cancel_epi (P.map c)).mp
  apply actualFieldPointPullbackSheafificationMap_ext q A V
    (P.map c ≫ d₁) (P.map c ≫ d₂)
  intro U hU a
  have hzero (d : P.obj (F.obj A) ⟶ V) :
      (moduleSpecΓFunctor (R := .of L)).map d
        (actualPointLocalSectionClass q (F.obj A) U hU
          ((sa.unit.app A).app (op U) (0 : A.obj (op U)))) = 0 := by
    let s := (sa.unit.app A).app (op U)
    let u := ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app
      (F.obj A)).val.app (op U)
    let v := (P.obj (F.obj A)).val.map (eqToHom (congrArg op hU))
    let f := ((moduleSpecΓFunctor (R := .of L)).map d).hom
    change f (v.hom (u.hom (s.hom 0))) = 0
    calc
      f (v.hom (u.hom (s.hom 0))) = f (v.hom (u.hom 0)) :=
        congrArg (fun x => f (v.hom (u.hom x))) s.hom.map_zero
      _ = f (v.hom 0) := congrArg (fun x => f (v.hom x)) u.hom.map_zero
      _ = f 0 := congrArg f v.hom.map_zero
      _ = 0 := f.map_zero
  induction a using TensorProduct.induction_on with
  | zero => exact (hzero (P.map c ≫ d₁)).trans (hzero (P.map c ≫ d₂)).symm
  | add a b ha hb =>
      simpa only [actualPointLocalSectionClass, map_add] using congrArg₂ (· + ·) ha hb
  | tmul wn t =>
      induction wn using TensorProduct.induction_on with
      | zero =>
          simpa only [TensorProduct.zero_tmul] using
            (hzero (P.map c ≫ d₁)).trans (hzero (P.map c ≫ d₂)).symm
      | add a b ha hb =>
          simpa only [TensorProduct.add_tmul, actualPointLocalSectionClass, map_add]
            using congrArg₂ (· + ·) ha hb
      | tmul w n =>
          let z := (sa.unit.app A).app (op U)
            ((w ⊗ₜ[Γ(X, U)] n) ⊗ₜ[Γ(X, U)] t)
          have hc := actualModuleSheafificationRightComparison_pureSection M N T U w n t
          have hn := actualPointLocalSectionClass_naturality q c U hU z
          have hp : (moduleSpecΓFunctor (R := .of L)).map (P.map c)
              (actualPointLocalSectionClass q (F.obj A) U hU z) =
              actualPointLocalSectionClass q (schemeModuleTensor (schemeModuleTensor M N) T)
                U hU (actualModuleLocalTensorSection (schemeModuleTensor M N) T U
                  (actualModuleLocalTensorSection M N U w n) t) :=
            hn.trans (congrArg (actualPointLocalSectionClass q
              (schemeModuleTensor (schemeModuleTensor M N) T) U hU) hc)
          simp only [Functor.map_comp, ModuleCat.comp_apply]
          change ((moduleSpecΓFunctor (R := .of L)).map d₁).hom
              (((moduleSpecΓFunctor (R := .of L)).map (P.map c)).hom
                (actualPointLocalSectionClass q (F.obj A) U hU z)) =
            ((moduleSpecΓFunctor (R := .of L)).map d₂).hom
              (((moduleSpecΓFunctor (R := .of L)).map (P.map c)).hom
                (actualPointLocalSectionClass q (F.obj A) U hU z))
          exact (congrArg ((moduleSpecΓFunctor (R := .of L)).map d₁).hom hp).trans
            ((h U hU w n t).trans
              (congrArg ((moduleSpecΓFunctor (R := .of L)).map d₂).hom hp).symm)

end PfaffianDescent
