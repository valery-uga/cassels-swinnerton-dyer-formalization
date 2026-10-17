import PfaffianDescent.CorayAffineTargetQuotientTransport

/-! Actual top sections and their ORIGINAL chart scalar action.
STATUS: UNVERIFIED source only. No compiler was run by the author.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual top sections, with the original Γ(X,top)-module structure. -/
def schemeTopModuleFunctor (X : Scheme.{u}) : X.Modules ⥤ ModuleCat Γ(X, ⊤) where
  obj M := ModuleCat.of Γ(X, ⊤) Γ(M, ⊤)
  map φ := ModuleCat.ofHom (φ.val.app (op ⊤)).hom
  map_id M := by apply ModuleCat.hom_ext; rfl
  map_comp φ ψ := by apply ModuleCat.hom_ext; rfl

/-- The canonical isoSpec transport of actual sections preserves the ORIGINAL
chart scalar action. The coefficient identity is derived from toSpecΓ_appTop. -/
def affineTargetPushforwardTopSectionsLinearEquiv (X : Scheme.{u}) [IsAffine X]
    (M : X.Modules) :
    (moduleSpecΓFunctor (R := Γ(X, ⊤))).obj
      ((Scheme.Modules.pushforward X.isoSpec.hom).obj M) ≃ₗ[Γ(X, ⊤)]
    (schemeTopModuleFunctor X).obj M := by
  refine
    { toFun := id
      invFun := id
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := ?_ }
  intro a x
  let y : Γ(M, ⊤) := x
  change (X.isoSpec.hom.appTop.hom
    ((Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom a)) • y = a • y
  rw [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
  exact congrArg (fun t : Γ(X, ⊤) => t • y)
    (ConcreteCategory.congr_hom (Scheme.ΓSpecIso Γ(X, ⊤)).inv_hom_id a)

/-- The original-scalar section identification is natural for actual module
maps, including actual quotient projections. -/
def affineTargetPushforwardTopSectionsNatIso (X : Scheme.{u}) [IsAffine X] :
    Scheme.Modules.pushforward X.isoSpec.hom ⋙
      moduleSpecΓFunctor (R := Γ(X, ⊤)) ≅ schemeTopModuleFunctor X := by
  refine NatIso.ofComponents
    (fun M => (affineTargetPushforwardTopSectionsLinearEquiv X M).toModuleIso) ?_
  intro M N φ
  apply ModuleCat.hom_ext
  rfl

/-- Canonical target transport keeps the ORIGINAL coordinate-ring map of f.
Thus using isoSpec does not replace Γ(X,top) -> Γ(Y,top) by unrelated scalars. -/
theorem affineSourceCoordinateMap_comp_isoSpec {X Y : Scheme.{u}}
    [IsAffine X] (f : Y ⟶ X) :
    affineSourceCoordinateMap (f ≫ X.isoSpec.hom) = f.appTop := by
  dsimp only [affineSourceCoordinateMap]
  rw [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- ACTUAL top sections of the ACTUAL affine-target quotient SHEAF identify
with the actual section cokernel after canonical transport. The left side
uses the original chart scalar structure, proved above rather than assumed. -/
def affineTargetQuotientSheaf_originalSectionsIso {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X) :
    (schemeTopModuleFunctor X).obj
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≅
    cokernel ((moduleSpecΓFunctor (R := Γ(X, ⊤))).map
      (SheafOfModules.unitToPushforwardObjUnit (f ≫ X.isoSpec.hom).toRingCatSheafHom)) :=
  ((affineTargetPushforwardTopSectionsNatIso X).app _).symm ≪≫
    affineTargetQuotientSheaf_specSectionsIso f

/-- Actual affine top sections are right exact for this particular ACTUAL
normalization-style quotient: source and target are actual affine schemes.
The proof constructs every transport and its commuting square internally. -/
def affineTargetQuotientSheaf_topCokernelIso {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X) :
    (schemeTopModuleFunctor X).obj
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≅
    cokernel ((schemeTopModuleFunctor X).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := by
  let e := X.isoSpec.hom
  let F := Scheme.Modules.pushforward e
  let G := moduleSpecΓFunctor (R := Γ(X, ⊤))
  let T := schemeTopModuleFunctor X
  let E := affineTargetPushforwardTopSectionsNatIso X
  let OX := SheafOfModules.unit X.ringCatSheaf
  let OY := SheafOfModules.unit Y.ringCatSheaf
  let N := (Scheme.Modules.pushforward f).obj OY
  let qf := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let qe := SheafOfModules.unitToPushforwardObjUnit e.toRingCatSheafHom
  let qfe := SheafOfModules.unitToPushforwardObjUnit (f ≫ e).toRingCatSheafHom
  letI : IsIso qe := affineSource_unit_isIso_of_isIso e
  let C := (Scheme.Modules.pushforwardComp f e).app OY
  let eA := G.mapIso (asIso qe) ≪≫ E.app OX
  let eB := G.mapIso C.symm ≪≫ E.app N
  have hcomp : qfe ≫ C.inv = qe ≫ F.map qf := by
    exact C.comp_inv_eq.mpr
      ((affineSource_unit_comp f e).trans (Category.assoc qe (F.map qf) C.hom).symm)
  have hc : G.map qfe ≫ eB.hom = eA.hom ≫ T.map qf := by
    change G.map qfe ≫ (G.map C.inv ≫ E.hom.app N) =
      (G.map qe ≫ E.hom.app OX) ≫ T.map qf
    rw [← Category.assoc, ← G.map_comp, hcomp, G.map_comp, Category.assoc]
    have hn : G.map (F.map qf) ≫ E.hom.app N = E.hom.app OX ≫ T.map qf :=
      E.hom.naturality qf
    rw [hn, Category.assoc]
  exact affineTargetQuotientSheaf_originalSectionsIso f ≪≫
    cokernel.mapIso (G.map qfe) (T.map qf) eA eB hc

end PfaffianDescent.Coray
