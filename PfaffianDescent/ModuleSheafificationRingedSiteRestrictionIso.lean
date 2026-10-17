import PfaffianDescent.SheafModulePushforwardExact

/- SOURCE ONLY / UNVERIFIED. Sheafification commutes with actual ringed
site restriction. Restriction of scalars changes no additive sections;
the underlying sheaf comparison is promoted to a module-linear Iso. -/
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

def moduleSheafificationRingedSiteRestrictionComparison :
    (PresheafOfModules.sheafification (𝟙 S.obj)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P) ⟶
    (SheafOfModules.pushforward φ).obj
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 S.obj)).symm
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P))

private def ringedRestrictionUnderlyingIso :
    (SheafOfModules.toSheaf S).obj
      ((PresheafOfModules.sheafification (𝟙 S.obj)).obj
        ((PresheafOfModules.pushforward φ.hom).obj P)) ≅
    (SheafOfModules.toSheaf S).obj
      ((SheafOfModules.pushforward φ).obj
        ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P)) := by
  let eL := (PresheafOfModules.sheafificationCompToSheaf
    (𝟙 S.obj)).app ((PresheafOfModules.pushforward φ.hom).obj P)
  let eC := (F.pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{u} J K).app P.presheaf
  let eR := (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).app P
  exact eL ≪≫ eC ≪≫ (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).mapIso eR.symm

private theorem ringedRestrictionUnderlyingComparison :
    (SheafOfModules.toSheaf S).map
      (moduleSheafificationRingedSiteRestrictionComparison F φ P) =
      (ringedRestrictionUnderlyingIso F φ P).hom := by
  have h := PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm
    (α := 𝟙 S.obj)
    (F := (SheafOfModules.pushforward φ).obj
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P))
    ((PresheafOfModules.pushforward φ.hom).map
      ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app P))
  dsimp [moduleSheafificationRingedSiteRestrictionComparison, ringedRestrictionUnderlyingIso]
  erw [h]
  apply ((CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{u}).homEquiv _ _).injective
  refine (Equiv.apply_symm_apply _ _).trans ?_
  dsimp
  erw [Adjunction.homEquiv_unit]
  dsimp [PresheafOfModules.sheafificationCompToSheaf]
  exact F.toSheafify_pullbackSheafificationCompatibility AddCommGrpCat.{u} J K P.presheaf |>.symm

def moduleSheafificationRingedSiteRestrictionIso :
    (PresheafOfModules.sheafification (𝟙 S.obj)).obj
      ((PresheafOfModules.pushforward φ.hom).obj P) ≅
    (SheafOfModules.pushforward φ).obj
      ((PresheafOfModules.sheafification (𝟙 R.obj)).obj P) := by
  letI : IsIso (moduleSheafificationRingedSiteRestrictionComparison F φ P) := by
    rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf S)]
    rw [ringedRestrictionUnderlyingComparison]
    exact Iso.isIso_hom _
  exact asIso (moduleSheafificationRingedSiteRestrictionComparison F φ P)

end PfaffianDescent
