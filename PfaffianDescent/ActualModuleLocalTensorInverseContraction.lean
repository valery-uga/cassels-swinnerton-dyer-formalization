import PfaffianDescent.SchemeModuleTensorInverseContraction
import PfaffianDescent.ActualModuleLocalTensorSection

/-! SOURCE ONLY / UNVERIFIED. The genuine canonical inverse-pairing
contraction on local pure sections, including both sheafification steps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite MonoidalCategory
open scoped TensorProduct
universe u
variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma sheafification_map_counit_evaluation
    (A : PresheafOfModules X.ringCatSheaf.obj) (M : X.Modules)
    (h : A ⟶ M.val) (U : X.Opens) (a : A.obj (op U)) :
    let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
    (F.map h ≫ adj.counit.app M).val.app (op U)
      ((adj.unit.app A).app (op U) a) = h.app (op U) a := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have hc : adj.homEquiv M.val M (adj.counit.app M) = 𝟙 M.val := by
    have ht := schemeModuleSheafificationHomEquiv_counit_comp (𝟙 M)
    dsimp only at ht
    have hcomp : adj.counit.app M ≫ 𝟙 M = adj.counit.app M :=
      Category.comp_id _
    have ht' : adj.homEquiv M.val M (adj.counit.app M) =
        SheafOfModules.Hom.val (𝟙 M : M ⟶ M) :=
      (congrArg (adj.homEquiv M.val M) hcomp).symm.trans ht
    exact ht'.trans (SheafOfModules.id_val M)
  have hh : adj.homEquiv A M (F.map h ≫ adj.counit.app M) = h := by
    rw [adj.homEquiv_naturality_left, hc, Category.comp_id]
  have hev := congrArg (fun v => v.app (op U) a) hh
  exact hev

/- The native inverse-pairing contraction really contracts the two actual
local twist sections using the actual pairing coefficient. -/
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualModuleLocalTensorInverseContraction
    (M N P : X.Modules)
    (e : schemeModuleTensor N P ≅ SheafOfModules.unit X.ringCatSheaf)
    [IsIso (schemeModuleTensorSheafificationRightComparison
      (PresheafOfModules.Monoidal.tensorObj M.val N.val) P)]
    (U : X.Opens) (m : M.val.obj (op U))
    (n : N.val.obj (op U)) (p : P.val.obj (op U)) :
    (schemeModuleTensorContraction M N P e).val.app (op U)
      (actualModuleLocalTensorSection (schemeModuleTensor M N) P U
        (actualModuleLocalTensorSection M N U m n) p) =
    (e.hom.val.app (op U) (actualModuleLocalTensorSection N P U n p)) • m := by
  let F := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let Q := PresheafOfModules.Monoidal.tensorObj M.val N.val
  let A := PresheafOfModules.Monoidal.tensorObj Q P.val
  let B := PresheafOfModules.Monoidal.tensorObj (F.obj Q).val P.val
  let c := schemeModuleTensorSheafificationRightComparison Q P
  let cr : A ⟶ B := PresheafOfModules.Monoidal.tensorHom
    (adj.unit.app Q) (𝟙 P.val)
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModules.monoidalCategory
  let h : A ⟶ M.val := (α_ M.val N.val P.val).hom ≫
    PresheafOfModules.Monoidal.tensorHom (𝟙 M.val)
      (schemeModuleTensorPairingRaw N P e) ≫ (ρ_ M.val).hom
  have hfactor : c ≫ schemeModuleTensorContraction M N P e =
      F.map h ≫ adj.counit.app M := by
    dsimp only [c, h, Q, F, adj, schemeModuleTensorContraction,
      schemeModuleTensorRawAssociator]
    simp only [Functor.mapIso_hom, Functor.map_comp, Category.assoc,
      IsIso.hom_inv_id_assoc]
  let a : A.obj (op U) := (m ⊗ₜ[Γ(X, U)] n) ⊗ₜ[Γ(X, U)] p
  have hpre : c.val.app (op U) ((adj.unit.app A).app (op U) a) =
      actualModuleLocalTensorSection (schemeModuleTensor M N) P U
        (actualModuleLocalTensorSection M N U m n) p := by
    have hn := congrArg (fun v => v.app (op U) a) (adj.unit.naturality cr)
    exact hn.symm
  calc
    (schemeModuleTensorContraction M N P e).val.app (op U)
        (actualModuleLocalTensorSection (schemeModuleTensor M N) P U
          (actualModuleLocalTensorSection M N U m n) p) =
      (c ≫ schemeModuleTensorContraction M N P e).val.app (op U)
        ((adj.unit.app A).app (op U) a) :=
      congrArg ((schemeModuleTensorContraction M N P e).val.app (op U)) hpre.symm
    _ = (F.map h ≫ adj.counit.app M).val.app (op U)
        ((adj.unit.app A).app (op U) a) :=
      congrArg (fun v => v.val.app (op U) ((adj.unit.app A).app (op U) a)) hfactor
    _ = h.app (op U) a := sheafification_map_counit_evaluation A M h U a
    _ = (e.hom.val.app (op U)
        (actualModuleLocalTensorSection N P U n p)) • m := by
      rfl

end PfaffianDescent
