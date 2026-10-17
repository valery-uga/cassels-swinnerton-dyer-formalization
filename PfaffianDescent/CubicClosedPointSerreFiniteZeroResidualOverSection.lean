import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualPullbackRestriction
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodSectionNaturality
import PfaffianDescent.SchemeModuleLocalIsoGerm

/-! # The actual section morphism under the over/restriction equivalence -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_over_unit_comparison
    {X : Scheme.{u}} (U : X.Opens) :
    ((Scheme.Modules.overFunctorEquiv U).app
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).hom =
        (Scheme.Modules.restrictUnitIso U.ι).inv := by
  ext V m
  simp only [Scheme.Modules.overFunctorEquiv, Iso.trans_hom,
    NatTrans.comp_app, SheafOfModules.pushforwardComp_hom_app_val_app,
    SheafOfModules.pushforwardCongr_hom_app_val_app]
  change m = (U.ι.appIso V).inv m
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  rfl

@[reassoc]
theorem cubicClosedPointSerreFiniteZeroResidual_over_section_hom
    {X : Scheme.{u}} (U : X.Opens) (E : X.Modules) (s : E.sections) :
    (((Scheme.Modules.overEquiv U).functor.obj (E.over U)).unitHomEquiv.symm
      (restrictSectionToOpen U s)) ≫ ((Scheme.Modules.overFunctorEquiv U).app E).hom =
      (Scheme.Modules.restrictUnitIso U.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (E.unitHomEquiv.symm s) := by
  unfold restrictSectionToOpen
  rw [Equiv.symm_apply_apply]
  have h := (Scheme.Modules.overFunctorEquiv U).hom.naturality (E.unitHomEquiv.symm s)
  change ((Scheme.Modules.overEquiv U).functor.map ((E.unitHomEquiv.symm s).over U)) ≫
    ((Scheme.Modules.overFunctorEquiv U).app E).hom =
      ((Scheme.Modules.overFunctorEquiv U).app
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf)).hom ≫
          (Scheme.Modules.restrictFunctor U.ι).map (E.unitHomEquiv.symm s) at h
  rw [cubicClosedPointSerreFiniteZeroResidual_over_unit_comparison] at h
  exact h

theorem cubicClosedPointSerreFiniteZeroResidual_over_section_top
    {X : Scheme.{u}} (U : X.Opens) (E : X.Modules) (s : E.sections) :
    (((Scheme.Modules.overFunctorEquiv U).app E).hom).val.app (Opposite.op ⊤)
      ((restrictSectionToOpen U s).val (Opposite.op ⊤)) =
      (schemeModuleRestrictTopSectionIso U E).inv (s.val (Opposite.op U)) := by
  let m := E.unitHomEquiv.symm s
  have h := congrArg (fun f => f.val.app (Opposite.op ⊤) (1 : Γ((U : Scheme), ⊤)))
    (cubicClosedPointSerreFiniteZeroResidual_over_section_hom U E s)
  change _ = ((Scheme.Modules.restrictUnitIso U.ι).inv ≫
    (Scheme.Modules.restrictFunctor U.ι).map m).val.app (Opposite.op ⊤)
      (1 : Γ((U : Scheme), ⊤)) at h
  have hm : m.val.app (Opposite.op U) (1 : Γ(X, U)) = s.val (Opposite.op U) := by
    exact congrArg (fun a => a.val (Opposite.op U)) (E.unitHomEquiv.apply_symm_apply s)
  rw [← cubicClosedPointSerreFreeNeighborhood_section_of_unit_hom E m U,
    hm] at h
  have hv := schemeModuleSectionOnOpenHom_value E U (s.val (Opposite.op U))
  have hv' :
      (schemeModuleSectionOnOpenHom E U (s.val (Opposite.op U))).val.app
        (Opposite.op ⊤) (1 : Γ((U : Scheme), ⊤)) =
      (schemeModuleRestrictTopSectionIso U E).inv (s.val (Opposite.op U)) := by
    apply (ConcreteCategory.bijective_of_isIso (schemeModuleRestrictTopSectionIso U E).hom).injective
    rw [Iso.inv_hom_id_apply]
    exact hv
  have hs := congrArg (fun a => a.val (Opposite.op ⊤))
    (((Scheme.Modules.overEquiv U).functor.obj (E.over U)).unitHomEquiv.apply_symm_apply
      (restrictSectionToOpen U s))
  change (((Scheme.Modules.overEquiv U).functor.obj (E.over U)).unitHomEquiv.symm
    (restrictSectionToOpen U s)).val.app (Opposite.op ⊤) (1 : Γ((U : Scheme), ⊤)) =
      (restrictSectionToOpen U s).val (Opposite.op ⊤) at hs
  have h' := h.trans hv'
  change (((Scheme.Modules.overFunctorEquiv U).app E).hom).val.app (Opposite.op ⊤)
    ((((Scheme.Modules.overEquiv U).functor.obj (E.over U)).unitHomEquiv.symm
      (restrictSectionToOpen U s)).val.app (Opposite.op ⊤) (1 : Γ((U : Scheme), ⊤))) = _ at h'
  rw [hs] at h'
  exact h'

end PfaffianDescent
