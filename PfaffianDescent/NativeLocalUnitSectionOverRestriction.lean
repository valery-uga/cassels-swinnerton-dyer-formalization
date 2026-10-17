import PfaffianDescent.SchemeModuleInternalHomRankOneTargetChart
import PfaffianDescent.SchemeModuleSectionOnOpen

/- SOURCE ONLY. Genuine comparison for a section originally defined ONLY
on its actual open, without extending it to a global section. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
open SchemeModuleInternalHom
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private instance nativeLocalSectionModule {X : Scheme.{u}} (N : X.Modules)
    (U : X.Opens) : Module Γ(X, U) (N.val.obj (op U)) :=
  (N.val.obj (op U)).isModule

/-- The WHOLE original local unitSectionOver corresponds to the SAME original
section-generated morphism on the actual open subscheme. No global extension
of b, desired comparison equality, frame or IsIso premise. -/
theorem nativeUnitSectionOver_overEquiv_toRestriction
    {X : Scheme.{u}} (N : X.Modules) (U : X.Opens)
    (b : N.val.obj (op U)) :
    (Scheme.Modules.overEquiv U).functor.map (unitSectionOver N U b) ≫
      ((Scheme.Modules.overFunctorEquiv U).app N).hom =
    (Scheme.Modules.restrictUnitIso U.ι).inv ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom ≫ schemeModuleSectionOnOpenHom N U b := by
  simp only [Iso.inv_hom_id_assoc]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  let hVU : U.ι ''ᵁ V.unop ≤ U := U.ι_image_le V.unop
  have h1 : (schemeModuleSectionOnOpenHom N U b).val.app V
      (1 : Γ((U : Scheme), V.unop)) = N.val.map (homOfLE hVU).op b := by
    exact schemeModuleSectionOnOpenHom_restrict_value' N U b V.unop
  have hr := schemeModuleUnitHom_apply_eq_smul_one (N.restrict U.ι)
    (schemeModuleSectionOnOpenHom N U b) V.unop r
  have hv : (schemeModuleSectionOnOpenHom N U b).val.app V r =
      (show Γ(X, U.ι ''ᵁ V.unop) from r) •
        (show N.val.obj (op (U.ι ''ᵁ V.unop)) from N.val.map (homOfLE hVU).op b) := by
    rw [h1] at hr
    have h := congrArg
      (fun z : (N.restrict U.ι).val.obj V => (N.restrictAppIso U.ι V.unop).hom z) hr
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply] at h
    simp only [Scheme.Opens.ι_appIso, Scheme.Modules.restrictAppIso,
      Iso.refl_inv, Iso.refl_hom] at h
    convert h using 1 <;> rfl
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    Scheme.Modules.overFunctorEquiv, Iso.trans_hom, NatTrans.comp_app,
    SheafOfModules.pushforwardComp_hom_app_val_app,
    SheafOfModules.pushforwardCongr_hom_app_val_app]
  change (show Γ(X, U.ι ''ᵁ V.unop) from r) •
      (show N.val.obj (op (U.ι ''ᵁ V.unop)) from N.val.map (homOfLE hVU).op b) =
    (schemeModuleSectionOnOpenHom N U b).val.app V r
  exact hv.symm

end PfaffianDescent
end
