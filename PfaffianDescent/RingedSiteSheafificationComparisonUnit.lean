import PfaffianDescent.ModuleSheafificationRingedSiteRestrictionIso

/- SOURCE ONLY / UNVERIFIED. The ringed site comparison commutes with
actual sheafification units; derived from its adjunction definition. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  (F : C ⥤ D) [F.IsContinuous J K] [F.IsCocontinuous J K]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  (P : PresheafOfModules R.obj)

theorem moduleSheafificationRingedSiteRestrictionIso_unit_comp :
    (PresheafOfModules.sheafificationAdjunction (𝟙 S.obj)).unit.app
      ((PresheafOfModules.pushforward φ.hom).obj P) ≫
      (moduleSheafificationRingedSiteRestrictionIso F φ P).hom.val =
    (PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P) := by
  have h := (PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)
    (P := (PresheafOfModules.pushforward φ.hom).obj P)
    (F := (SheafOfModules.pushforward φ).obj
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P))).apply_symm_apply
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P))
  change _ = _ at h
  exact h

end PfaffianDescent
