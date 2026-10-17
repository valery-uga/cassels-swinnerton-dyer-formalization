import PfaffianDescent.SchemeModuleSectionOnOpen
import PfaffianDescent.VoisinStandardOpenExtVanishing
import PfaffianDescent.NativeLocalUnitSectionOverRestriction

/- SOURCE ONLY. Actual section-generated Hom under an ORIGINAL scheme-Iso
chart, and ordinary native unit-frame detection. No global section extension. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact named-image equality of an ORIGINAL open Iso chart. -/
theorem nativeSchemeIsoOpenChart_image_top
    {X Y : Scheme.{u}} (U : X.Opens) (a : Y ≅ (U : Scheme)) :
    (a.hom ≫ U.ι) ''ᵁ ⊤ = U := by
  rw [Scheme.Hom.image_top_eq_opensRange,
    Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

/-- The ORIGINAL chart pullback of the ORIGINAL local section Hom takes 1
to the SAME original section, with only its internally proved image normalization. -/
theorem nativeSchemeIsoOpenChart_sectionHom_one
    {X Y : Scheme.{u}} (U : X.Opens) (a : Y ≅ (U : Scheme))
    (N : X.Modules) (b : N.val.obj (op U)) :
    (((Scheme.Modules.restrictUnitIso a.hom).inv ≫
      (Scheme.Modules.restrictFunctor a.hom).map (schemeModuleSectionOnOpenHom N U b) ≫
      ((Scheme.Modules.restrictFunctorComp a.hom U.ι).app N).inv).val.app (op ⊤))
        (1 : Γ(Y, ⊤)) =
    N.val.map (eqToHom (nativeSchemeIsoOpenChart_image_top U a)).op b := by
  have hs : (schemeModuleSectionOnOpenHom N U b).val.app (op (a.hom ''ᵁ ⊤))
      (1 : Γ((U : Scheme), a.hom ''ᵁ ⊤)) =
      N.presheaf.map (homOfLE (U.ι_image_le (a.hom ''ᵁ ⊤))).op b :=
    schemeModuleSectionOnOpenHom_restrict_value' N U b (a.hom ''ᵁ ⊤)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app]
  change (N.presheaf.map (eqToHom
    (show (a.hom ≫ U.ι) ''ᵁ ⊤ = U.ι ''ᵁ (a.hom ''ᵁ ⊤) from by simp)).op)
      ((schemeModuleSectionOnOpenHom N U b).val.app (op (a.hom ''ᵁ ⊤))
        ((a.hom.appIso ⊤).inv 1)) = _
  rw [map_one]
  rw [hs]
  change (N.presheaf.map _).hom ((N.presheaf.map _).hom b) =
    (N.presheaf.map _).hom b
  rw [← ConcreteCategory.comp_apply, ← N.presheaf.map_comp]
  congr 1

/-- Unit-source native morphism invertibility from an ACTUAL frame and its
actual computed top coefficient. Every other component follows internally. -/
theorem nativeSchemeUnitHom_isIso_of_frameTopValueOne
    {X : Scheme.{u}} (N : X.Modules)
    (e : N ≅ SheafOfModules.unit X.ringCatSheaf)
    (f : SheafOfModules.unit X.ringCatSheaf ⟶ N)
    (hf : e.hom.val.app (op ⊤) (f.val.app (op ⊤) (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤))) :
    IsIso f := by
  let c := f ≫ e.hom
  have hc : c.val.app (op ⊤) (1 : Γ(X, ⊤)) = (1 : Γ(X, ⊤)) := hf
  have heq : c = 𝟙 _ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    have h1 := schemeModuleUnitHom_restrict_one
      (SheafOfModules.unit X.ringCatSheaf) c V.unop
    rw [hc] at h1
    change c.val.app V (1 : Γ(X, V.unop)) =
      X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op 1 at h1
    have h1' : c.val.app V (1 : Γ(X, V.unop)) = (1 : Γ(X, V.unop)) := by
      simpa only [map_one] using h1
    have hr := schemeModuleUnitHom_apply_eq_smul_one
      (SheafOfModules.unit X.ringCatSheaf) c V.unop r
    change c.val.app V r = r
    rw [hr, h1']
    change (show Γ(X, V.unop) from r) * (1 : Γ(X, V.unop)) =
      (show Γ(X, V.unop) from r)
    exact mul_one _
  exact IsIso.of_isIso_fac_right heq

/-- Actual ORIGINAL over-site generator invertibility from a true scheme-Iso
chart frame and its computed coefficient. There is no supplied map equality or
upstairs generator IsIso; all native section comparisons are derived internally. -/
theorem nativeUnitSectionOver_isIso_of_schemeIsoChartFrameTopValueOne
    {X Y : Scheme.{u}} (U : X.Opens) (a : Y ≅ (U : Scheme))
    (f : Y ⟶ X) [IsOpenImmersion f] (hf : f = a.hom ≫ U.ι)
    (hU : f ''ᵁ ⊤ = U) (N : X.Modules) (b : N.val.obj (op U))
    (e : (Scheme.Modules.restrictFunctor f).obj N ≅ SheafOfModules.unit Y.ringCatSheaf)
    (hb : e.hom.val.app (op ⊤) (N.val.map (eqToHom hU).op b) = (1 : Γ(Y, ⊤))) :
    IsIso (SchemeModuleInternalHom.unitSectionOver N U b) := by
  cases hf
  let R := Scheme.Modules.restrictFunctor a.hom
  let j := schemeModuleSectionOnOpenHom N U b
  let u := Scheme.Modules.restrictUnitIso a.hom
  let t := (Scheme.Modules.restrictFunctorComp a.hom U.ι).app N
  let J : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.restrictFunctor (a.hom ≫ U.ι)).obj N :=
    u.inv ≫ R.map j ≫ t.inv
  have hJ : e.hom.val.app (op ⊤) (J.val.app (op ⊤) (1 : Γ(Y, ⊤))) = (1 : Γ(Y, ⊤)) := by
    rw [nativeSchemeIsoOpenChart_sectionHom_one]
    exact hb
  letI : IsIso J := nativeSchemeUnitHom_isIso_of_frameTopValueOne _ e J hJ
  letI : IsIso (R.map j ≫ t.inv) := IsIso.of_isIso_comp_left u.inv (R.map j ≫ t.inv)
  letI : IsIso (R.map j) := IsIso.of_isIso_comp_right (R.map j) t.inv
  letI : R.IsEquivalence :=
    (schemeModulesEquivalenceOfIsoRestrict a.symm).isEquivalence_functor
  letI : IsIso j := isIso_of_reflects_iso j R
  let E := Scheme.Modules.overEquiv U
  let c := ((Scheme.Modules.overFunctorEquiv U).app N).hom
  have h := nativeUnitSectionOver_overEquiv_toRestriction N U b
  letI : IsIso (E.functor.map (SchemeModuleInternalHom.unitSectionOver N U b) ≫ c) := by
    rw [h]
    infer_instance
  letI : IsIso (E.functor.map (SchemeModuleInternalHom.unitSectionOver N U b)) :=
    IsIso.of_isIso_comp_right (E.functor.map (SchemeModuleInternalHom.unitSectionOver N U b)) c
  exact isIso_of_reflects_iso (SchemeModuleInternalHom.unitSectionOver N U b) E.functor

end PfaffianDescent
end
