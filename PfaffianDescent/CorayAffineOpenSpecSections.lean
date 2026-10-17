import PfaffianDescent.CorayAffineOriginalTopSections
import PfaffianDescent.CorayOriginalOpenSections
import PfaffianDescent.AffineGammaPushforward

/-! Actual affine-open Spec presentation preserves ORIGINAL chart sections.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Actual pushforward of the actual restricted module along the ORIGINAL
chart isoSpec has actual sections isomorphic over ORIGINAL Γ(X,U) to Γ(M,U).
This composes actual canonical section maps and actual scalar restrictions. -/
def affineOpenSpecPushforward_sectionsIso
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) (M : X.Modules) :
    (moduleSpecΓFunctor (R := Γ(X, U))).obj
      ((Scheme.Modules.pushforward hU.isoSpec.hom).obj
        ((Scheme.Modules.restrictFunctor U.ι).obj M)) ≅
      (schemeOpenModuleFunctor X U).obj M := by
  letI : IsAffine U.toScheme := hU
  let MU := (Scheme.Modules.restrictFunctor U.ι).obj M
  let e := U.toScheme.isoSpec.hom
  let g := Spec.map U.topIso.inv
  let G := moduleSpecΓFunctor (R := Γ(X, U))
  let S := ModuleCat.restrictScalars U.topIso.inv.hom
  have he : hU.isoSpec.hom = e ≫ g := rfl
  exact G.mapIso ((Scheme.Modules.pushforwardCongr he).app MU) ≪≫
    G.mapIso ((Scheme.Modules.pushforwardComp e g).symm.app MU) ≪≫
    (affineGammaPushforwardNatIso U.topIso.inv).app
      ((Scheme.Modules.pushforward e).obj MU) ≪≫
    S.mapIso ((affineTargetPushforwardTopSectionsNatIso U.toScheme).app MU) ≪≫
    originalOpenRestrictTopSectionsIso X U M

/-- Actual affine-source quotient sheaf, transported along any actual
isomorphism of the target with Spec R, is in the tilde essential image.
Every counit isomorphism used here is DERIVED from the actual source affinity. -/
theorem affineIsoTargetQuotientSheaf_fromTildeGamma_isIso
    {R : CommRingCat.{u}} {X Y : Scheme.{u}} [IsAffine Y]
    (f : Y ⟶ X) (e : X ≅ Spec R) :
    IsIso (Scheme.Modules.fromTildeΓ (R := R)
      ((Scheme.Modules.pushforward e.hom).obj
        (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)))) := by
  let q := SheafOfModules.unitToPushforwardObjUnit (f ≫ e.hom).toRingCatSheafHom
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R)
      ((SheafOfModules.pushforward (f ≫ e.hom).toRingCatSheafHom).obj
        (SheafOfModules.unit Y.ringCatSheaf))) :=
    affineSourcePushforwardUnit_fromTildeGamma_isIso (f ≫ e.hom)
  exact isIso_fromTildeΓ_iff.mpr
    ⟨cokernel ((moduleSpecΓFunctor (R := R)).map q),
      ⟨affineCokernelFromTildeGammaIso q ≪≫ (schemeIsoTargetQuotientSheafIso f e).symm⟩⟩

end PfaffianDescent.Coray
