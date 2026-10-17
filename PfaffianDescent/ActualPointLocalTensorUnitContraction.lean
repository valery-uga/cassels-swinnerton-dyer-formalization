import PfaffianDescent.ActualModuleLocalTensorRightUnitAction
import PfaffianDescent.ActualPointLocalTensorPullbackAction
import PfaffianDescent.ActualPointTwistUntwistRatio

/- SOURCE ONLY / UNVERIFIED. Actual point untwisting of LOCAL pure
tensors uses the COMPUTED actual unit coefficient; no fixed generator,
coefficient-one or desired comparison certificate is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma actualPointTwistUntwistIso_localTensorSection
    {L : Type u} [Field L] (M T : (Spec (.of L)).Modules)
    (e : T ≅ SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (m : M.val.obj (op ⊤)) (t : T.val.obj (op ⊤)) :
    (actualPointTwistUntwistIso M T e).hom.val.app (op ⊤)
      (actualModuleLocalTensorSection M T ⊤ m t) =
      (e.hom.val.app (op ⊤) t) • m := by
  change (schemeModuleTensorUnitRightIso M).hom.val.app (op ⊤)
    ((schemeModuleTensorMap (𝟙 M) e.hom).val.app (op ⊤)
      (actualModuleLocalTensorSection M T ⊤ m t)) = _
  have h := actualModuleLocalTensorSection_naturality (𝟙 M) e.hom ⊤ m t
  exact (congrArg (fun z => (schemeModuleTensorUnitRightIso M).hom.val.app (op ⊤) z) h).trans
    (actualModuleLocalTensorRightUnitAction M ⊤ m (e.hom.val.app (op ⊤) t))

lemma actualPointLocalTensorUnitContraction
    {L : Type u} [Field L] {X : Scheme.{u}}
    (q : Spec (.of L) ⟶ X) (M T : X.Modules)
    (U : X.Opens) (hU : q ⁻¹ᵁ U = ⊤)
    (e : (Scheme.Modules.pullback q).obj T ≅
      SheafOfModules.unit (Spec (.of L)).ringCatSheaf)
    (m : M.val.obj (op U)) (t : T.val.obj (op U)) :
    (moduleSpecΓFunctor (R := .of L)).map
      (cubicClosedPointSerreFiniteZeroResidual_pullbackTensorMap q M T ≫
        (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj M)
          ((Scheme.Modules.pullback q).obj T) e).hom)
      (actualPointLocalSectionClass q (schemeModuleTensor M T) U hU
        (actualModuleLocalTensorSection M T U m t)) =
    (show Γ(Spec (.of L), ⊤) from
      e.hom.val.app (op ⊤) (actualPointLocalSectionClass q T U hU t)) •
      (show ((Scheme.Modules.pullback q).obj M).val.obj (op ⊤) from
        actualPointLocalSectionClass q M U hU m) := by
  rw [CategoryTheory.Functor.map_comp, ModuleCat.comp_apply]
  have h := actualPointLocalTensorPullbackAction q M T U hU m t
  exact (congrArg (fun z => (moduleSpecΓFunctor (R := .of L)).map
    (actualPointTwistUntwistIso ((Scheme.Modules.pullback q).obj M)
      ((Scheme.Modules.pullback q).obj T) e).hom z) h).trans
    (actualPointTwistUntwistIso_localTensorSection
      ((Scheme.Modules.pullback q).obj M) ((Scheme.Modules.pullback q).obj T) e _ _)

end PfaffianDescent
