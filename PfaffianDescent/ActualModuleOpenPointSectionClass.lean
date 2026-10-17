import PfaffianDescent.ActualModulePointSectionClass
import PfaffianDescent.SchemeModuleLocalIsoCoordinate
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPointRestrictSection

/- SOURCE ONLY / UNVERIFIED. Sections on the literal original open are
sent to the SAME actual original point fiber, through the genuine
restriction/pullback comparison. The scalar map is defined from q.appTop. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite BundleSectionZeroLocus
universe u

def actualOpenSectionUnitHomAddEquiv
    {K : Type u} [Field K] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (U : X.Opens) (M : X.Modules) :
    Γ(M, U) ≃+ (schemeModuleUnit (U : Scheme) ⟶ M.restrict U.ι) :=
  (schemeModuleRestrictTopSectionIso U M).symm.addCommGroupIsoToAddEquiv.trans
    (schemeModuleGlobalSectionsAddEquivOpenTop (U.ι ≫ g) (M.restrict U.ι)).symm

def actualOpenRegularFunction
    {X : Scheme.{u}} (U : X.Opens) (a : Γ(X, U)) : Γ((U : Scheme), ⊤) :=
  (U.ι.appIso ⊤).hom
    ((X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).inv a)

lemma actualOpenSectionUnitHomAddEquiv_smul
    {K : Type u} [Field K] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (U : X.Opens) (M : X.Modules)
    (a : Γ(X, U)) (s : Γ(M, U)) :
    actualOpenSectionUnitHomAddEquiv g U M (a • s) =
      unitEndomorphismOfRegularFunction (actualOpenRegularFunction U a) ≫
        actualOpenSectionUnitHomAddEquiv g U M s := by
  let r := actualOpenRegularFunction U a
  let s' := actualOpenSectionUnitHomAddEquiv g U M s
  let N := M.restrict U.ι
  have hm : (schemeModuleRestrictTopSectionIso U M).inv (a • s) =
      r • (schemeModuleRestrictTopSectionIso U M).inv s := by
    dsimp only [schemeModuleRestrictTopSectionIso, Iso.trans_inv]
    simp only [ConcreteCategory.comp_apply, Functor.mapIso_inv, Iso.op_inv]
    rw [Scheme.Modules.map_smul]
    exact Scheme.Modules.smul_restrictAppIso_inv_apply U.ι M ⊤ _ _
  apply (schemeModuleGlobalSectionsAddEquivOpenTop (U.ι ≫ g) N).injective
  change (schemeModuleRestrictTopSectionIso U M).inv (a • s) =
    s'.app ⊤ ((unitEndomorphismOfRegularFunction r).app ⊤ 1)
  rw [unitEndomorphismValue_ofRegularFunction, hm]
  have hs : s'.app ⊤ (1 : Γ((U : Scheme), ⊤)) =
      (schemeModuleRestrictTopSectionIso U M).inv s := by
    exact (schemeModuleGlobalSectionsAddEquivOpenTop (U.ι ≫ g) N).apply_symm_apply _
  rw [← hs]
  simpa only [smul_eq_mul, mul_one] using
    Scheme.Modules.Hom.app_smul s' r (1 : Γ((U : Scheme), ⊤))

def actualOpenPointResidue
    {L : Type u} [Field L] {X : Scheme.{u}} (U : X.Opens)
    (q : Spec (.of L) ⟶ (U : Scheme)) : Γ(X, U) →+* L :=
  (Scheme.ΓSpecIso (.of L)).hom.hom.comp
    (q.appTop.hom.comp ((U.ι.appIso ⊤).hom.hom.comp
      (X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op).inv.hom))

def actualModuleOpenPointSectionClass
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (U : X.Opens)
    (q : Spec (.of L) ⟶ (U : Scheme)) (M : X.Modules) :
    Γ(M, U) →+
      (moduleSpecΓFunctor (R := .of L)).obj
        ((Scheme.Modules.pullback (q ≫ U.ι)).obj M) :=
  ((moduleSpecΓFunctor (R := .of L)).map
    (cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso U.ι q M).inv).hom.toAddHom.comp
    ((actualModulePointSectionClass q (M.restrict U.ι)).comp
      (actualOpenSectionUnitHomAddEquiv g U M).toAddHom)

lemma actualModuleOpenPointSectionClass_smul
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of K)) (U : X.Opens)
    (q : Spec (.of L) ⟶ (U : Scheme)) (M : X.Modules)
    (a : Γ(X, U)) (s : Γ(M, U)) :
    actualModuleOpenPointSectionClass g U q M (a • s) =
      actualOpenPointResidue U q a • actualModuleOpenPointSectionClass g U q M s := by
  change (moduleSpecΓFunctor (R := .of L)).map
      (cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso U.ι q M).inv
      (actualModulePointSectionClass q (M.restrict U.ι)
        (actualOpenSectionUnitHomAddEquiv g U M (a • s))) = _
  rw [actualOpenSectionUnitHomAddEquiv_smul,
    actualModulePointSectionClass_regularFunction]
  exact ((moduleSpecΓFunctor (R := .of L)).map
    (cubicClosedPointSerreSurfaceJetCotangent_pointOpenRestrictPullbackIso U.ι q M).inv).hom.map_smul _ _

end PfaffianDescent
