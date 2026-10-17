import PfaffianDescent.SchemeModuleRestrictStalkLinear
import PfaffianDescent.FieldPointSectionRepresenterKoszul

/-! # Section and stalk coordinates from an actual local module isomorphism -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
namespace PfaffianDescent
universe u

/-- The additive comparison between sections on an open and top sections of
the restricted module, with the image of the top open identified explicitly. -/
def schemeModuleRestrictTopSectionIso {X : Scheme.{u}} (U : X.Opens)
    (M : X.Modules) : Γ(M.restrict U.ι, ⊤) ≅ Γ(M, U) :=
  M.restrictAppIso U.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

/-- A local module isomorphism gives additive coordinates on its open. -/
def schemeModuleLocalSectionAddEquiv {X : Scheme.{u}} (U : X.Opens)
    (M N : X.Modules) (e : M.restrict U.ι ≅ N.restrict U.ι) :
    Γ(M, U) ≃+ Γ(N, U) :=
  ((schemeModuleRestrictTopSectionIso U M).symm ≪≫
    ((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e).app (op ⊤) ≪≫
    schemeModuleRestrictTopSectionIso U N).addCommGroupIsoToAddEquiv

set_option backward.isDefEq.respectTransparency false in
/-- Local section coordinates respect the ambient ring of sections. -/
theorem schemeModuleLocalSectionAddEquiv_smul {X : Scheme.{u}} (U : X.Opens)
    (M N : X.Modules) (e : M.restrict U.ι ≅ N.restrict U.ι)
    (a : Γ(X, U)) (y : Γ(M, U)) :
    schemeModuleLocalSectionAddEquiv U M N e (a • y) =
      a • schemeModuleLocalSectionAddEquiv U M N e y := by
  let a' := (X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).inv a
  let r := (U.ι.appIso ⊤).hom a'
  have hm : (schemeModuleRestrictTopSectionIso U M).inv (a • y) =
      r • (schemeModuleRestrictTopSectionIso U M).inv y := by
    dsimp only [schemeModuleRestrictTopSectionIso, Iso.trans_inv]
    simp only [ConcreteCategory.comp_apply, Functor.mapIso_inv, Iso.op_inv]
    rw [Scheme.Modules.map_smul]
    exact Scheme.Modules.smul_restrictAppIso_inv_apply U.ι M ⊤ a' _
  have hn (z : Γ(N.restrict U.ι, ⊤)) :
      (schemeModuleRestrictTopSectionIso U N).hom (r • z) =
        a • (schemeModuleRestrictTopSectionIso U N).hom z := by
    dsimp only [schemeModuleRestrictTopSectionIso, Iso.trans_hom]
    simp only [ConcreteCategory.comp_apply, Functor.mapIso_hom, Iso.op_hom]
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply, Scheme.Modules.map_smul]
    have ha : (X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).hom
        ((U.ι.appIso ⊤).inv r) = a := by
      dsimp only [r, a']
      rw [Iso.hom_inv_id_apply]
      exact Iso.inv_hom_id_apply _ a
    change (X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).hom
        ((U.ι.appIso ⊤).inv r) • _ = a • _
    rw [ha]
  change (schemeModuleRestrictTopSectionIso U N).hom
      (e.hom.val.app (op ⊤) ((schemeModuleRestrictTopSectionIso U M).inv (a • y))) = _
  rw [hm, (e.hom.val.app (op ⊤)).hom.map_smul]
  exact hn _

/-- The same local isomorphism gives additive coordinates on ambient stalks. -/
def schemeModuleLocalStalkAddEquiv {X : Scheme.{u}} (U : X.Opens) (x : U)
    (M N : X.Modules) (e : M.restrict U.ι ≅ N.restrict U.ι) :
    M.presheaf.stalk (U.ι x) ≃+ N.presheaf.stalk (U.ι x) :=
  (((Scheme.Modules.restrictStalkNatIso U.ι x).app M).symm ≪≫
    (TopCat.Presheaf.stalkFunctor (X := (U : Scheme).toTopCat) Ab.{u} x).mapIso
      ((Scheme.Modules.toPresheaf (U : Scheme)).mapIso e) ≪≫
    (Scheme.Modules.restrictStalkNatIso U.ι x).app N).addCommGroupIsoToAddEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The ambient stalk coordinates are linear for the actual ambient local ring. -/
theorem schemeModuleLocalStalkAddEquiv_smul {X : Scheme.{u}}
    (U : X.Opens) (x : U) (M N : X.Modules)
    (e : M.restrict U.ι ≅ N.restrict U.ι)
    (a : X.presheaf.stalk (U.ι x)) (y : M.presheaf.stalk (U.ι x)) :
    letI := schemeModuleStalkModule M (U.ι x)
    letI := schemeModuleStalkModule N (U.ι x)
    schemeModuleLocalStalkAddEquiv U x M N e (a • y) =
      a • schemeModuleLocalStalkAddEquiv U x M N e y := by
  dsimp only
  letI := schemeModuleStalkModule M (U.ι x)
  letI := schemeModuleStalkModule N (U.ι x)
  letI := schemeModuleStalkModule (M.restrict U.ι) x
  letI := schemeModuleStalkModule (N.restrict U.ι) x
  change (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app N
      (schemeModuleStalkLinearMap e.hom x
        ((Scheme.Modules.restrictStalkNatIso U.ι x).inv.app M (a • y))) = _
  rw [schemeModuleRestrictStalk_inv_smul,
    (schemeModuleStalkLinearMap e.hom x).map_smul]
  exact schemeModuleRestrictStalk_hom_smul U x N a _

/-- The actual local isomorphism, now in the ambient local-ring module category. -/
def schemeModuleLocalStalkModuleIso {X : Scheme.{u}} (U : X.Opens) (x : U)
    (M N : X.Modules) (e : M.restrict U.ι ≅ N.restrict U.ι) :
    (schemeModuleStalkModuleFunctor X (U.ι x)).obj M ≅
      (schemeModuleStalkModuleFunctor X (U.ι x)).obj N := by
  letI := schemeModuleStalkModule M (U.ι x)
  letI := schemeModuleStalkModule N (U.ι x)
  let l : M.presheaf.stalk (U.ι x) ≃ₗ[X.presheaf.stalk (U.ι x)]
      N.presheaf.stalk (U.ι x) :=
    { toAddEquiv := schemeModuleLocalStalkAddEquiv U x M N e
      map_smul' := schemeModuleLocalStalkAddEquiv_smul U x M N e }
  exact LinearEquiv.toModuleIso l

end PfaffianDescent
