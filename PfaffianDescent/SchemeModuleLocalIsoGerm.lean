import PfaffianDescent.SchemeModuleLocalIsoCoordinate

/-! # Compatibility of actual local section and stalk coordinates -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
/-- The top-section restriction comparison commutes with taking the ambient germ. -/
theorem schemeModuleRestrictTopSectionIso_germ {X : Scheme.{u}}
    (U : X.Opens) (x : U) (M : X.Modules) (y : Γ(M, U)) :
    (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M
      ((M.restrict U.ι).presheaf.germ ⊤ x trivial
        ((schemeModuleRestrictTopSectionIso U M).inv y)) =
      M.presheaf.germ U (U.ι x) x.2 y := by
  have h := congrArg (fun g => g.hom ((schemeModuleRestrictTopSectionIso U M).inv y))
    (Scheme.Modules.germ_restrictStalkNatIso_hom_app U.ι x M (U := ⊤) trivial)
  change _ = M.presheaf.germ (U.ι ''ᵁ ⊤) (U.ι x) _
    (M.presheaf.map (eqToIso U.ι_image_top.symm).inv.op y) at h
  exact h.trans (M.presheaf.germ_res_apply
    (eqToIso U.ι_image_top.symm).inv (U.ι x) (by simpa using x.2) y)

set_option backward.isDefEq.respectTransparency false in
/-- The section and stalk coordinates of one local isomorphism give the same germ. -/
theorem schemeModuleLocalStalkAddEquiv_germ {X : Scheme.{u}}
    (U : X.Opens) (x : U) (M N : X.Modules)
    (e : M.restrict U.ι ≅ N.restrict U.ι) (y : Γ(M, U)) :
    schemeModuleLocalStalkAddEquiv U x M N e
      (M.presheaf.germ U (U.ι x) x.2 y) =
      N.presheaf.germ U (U.ι x) x.2
        (schemeModuleLocalSectionAddEquiv U M N e y) := by
  let ym := (schemeModuleRestrictTopSectionIso U M).inv y
  let z := e.hom.val.app (op ⊤) ym
  have hm : (Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M
      (M.presheaf.germ U (U.ι x) x.2 y) =
      (M.restrict U.ι).presheaf.germ ⊤ x trivial ym := by
    rw [← schemeModuleRestrictTopSectionIso_germ U x M y]
    exact Iso.hom_inv_id_apply _ _
  have hsec : (schemeModuleRestrictTopSectionIso U N).inv
      (schemeModuleLocalSectionAddEquiv U M N e y) = z := by
    change (schemeModuleRestrictTopSectionIso U N).inv
      ((schemeModuleRestrictTopSectionIso U N).hom z) = z
    exact Iso.hom_inv_id_apply _ _
  change (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app N
      ((TopCat.Presheaf.stalkFunctor (X := (U : Scheme).toTopCat) Ab.{u} x).map
        ((Scheme.Modules.toPresheaf (U : Scheme)).map e.hom)
        ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M
          (M.presheaf.germ U (U.ι x) x.2 y))) = _
  rw [hm]
  have hg := TopCat.Presheaf.stalkFunctor_map_germ_apply
    (X := (U : Scheme).toTopCat) (C := Ab.{u})
    (F := (M.restrict U.ι).presheaf) (G := (N.restrict U.ι).presheaf)
    ⊤ x trivial ((Scheme.Modules.toPresheaf (U : Scheme)).map e.hom) ym
  have hn := schemeModuleRestrictTopSectionIso_germ U x N
    (schemeModuleLocalSectionAddEquiv U M N e y)
  rw [hsec] at hn
  exact (congrArg ((Scheme.Modules.restrictStalkNatIso U.ι x).hom.app N) hg).trans hn

/-- A chosen actual unit trivialization supplies an ambient local-ring stalk coordinate. -/
def schemeModuleLocalUnitStalkIso {X : Scheme.{u}} (U : X.Opens) (x : U)
    (Y : X.Modules)
    (eY : Y.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj Y ≅
      ModuleCat.of (X.presheaf.stalk (U.ι x)) (X.presheaf.stalk (U.ι x)) :=
  schemeModuleLocalStalkModuleIso U x Y (SheafOfModules.unit X.ringCatSheaf)
    (eY ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm) ≪≫
      schemeModuleUnitStalkIso X (U.ι x)

/-- The matching actual scalar coordinate on sections of the trivializing open. -/
def schemeModuleLocalUnitSectionAddEquiv {X : Scheme.{u}} (U : X.Opens)
    (Y : X.Modules)
    (eY : Y.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    Γ(Y, U) ≃+ Γ(X, U) :=
  schemeModuleLocalSectionAddEquiv U Y (SheafOfModules.unit X.ringCatSheaf)
    (eY ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The actual local unit coordinates respect multiplication by ring sections. -/
theorem schemeModuleLocalUnitSectionAddEquiv_smul {X : Scheme.{u}}
    (U : X.Opens) (Y : X.Modules)
    (eY : Y.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (a : Γ(X, U)) (y : Γ(Y, U)) :
    schemeModuleLocalUnitSectionAddEquiv U Y eY (a • y) =
      a * schemeModuleLocalUnitSectionAddEquiv U Y eY y :=
  schemeModuleLocalSectionAddEquiv_smul U Y (SheafOfModules.unit X.ringCatSheaf)
    (eY ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm) a y

set_option backward.isDefEq.respectTransparency false in
/-- Taking a coefficient germ in the actual stalk coordinate agrees with taking
the ring germ of its actual section coordinate. -/
theorem schemeModuleLocalUnitStalkCoordinate_germ {X : Scheme.{u}}
    (U : X.Opens) (x : U) (Y : X.Modules)
    (eY : Y.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (y : Γ(Y, U)) :
    schemeModuleSectionStalkCoordinateAddHom U (U.ι x) x.2 Y
      (schemeModuleLocalUnitStalkIso U x Y eY) y =
      X.presheaf.germ U (U.ι x) x.2
        (schemeModuleLocalUnitSectionAddEquiv U Y eY y) := by
  change (schemeModuleUnitStalkIso X (U.ι x)).hom
      (schemeModuleLocalStalkAddEquiv U x Y (SheafOfModules.unit X.ringCatSheaf)
        (eY ≪≫ (Scheme.Modules.restrictUnitIso U.ι).symm)
        (Y.presheaf.germ U (U.ι x) x.2 y)) = _
  rw [schemeModuleLocalStalkAddEquiv_germ]
  exact schemeModuleSectionStalkCoordinateAddHom_unit U (U.ι x) x.2 _

end PfaffianDescent
