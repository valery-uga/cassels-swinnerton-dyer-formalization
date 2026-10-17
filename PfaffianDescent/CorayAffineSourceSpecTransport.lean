import PfaffianDescent.CorayAffineSheafCokernelSections
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! Canonical affine-source transport of the actual structure-sheaf unit.
STATUS: UNVERIFIED source only. No compiler was run by the author.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual coordinate-ring homomorphism of an affine source over Spec R. -/
def affineSourceCoordinateMap {R : CommRingCat.{u}} {Y : Scheme.{u}}
    (f : Y ⟶ Spec R) : R ⟶ Γ(Y, ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ f.appTop

/-- The canonical isoSpec of the source preserves the original morphism. -/
theorem affineSourceCoordinateMap_spec {R : CommRingCat.{u}}
    {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ Spec R) :
    f = Y.isoSpec.hom ≫ Spec.map (affineSourceCoordinateMap f) := by
  dsimp only [affineSourceCoordinateMap]
  rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
    Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp]
  simp

/-- The canonical structure-sheaf unit along an actual scheme isomorphism
is itself an isomorphism; this is proved on its actual section functions. -/
theorem affineSource_unit_isIso_of_isIso {Y Z : Scheme.{u}}
    (e : Y ⟶ Z) [IsIso e] :
    IsIso (SheafOfModules.unitToPushforwardObjUnit e.toRingCatSheafHom) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  letI : IsIso (e.app U) := e.isIso_app U (by
    rw [e.opensRange_of_isIso]
    exact le_top)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (fun r : Γ(Z, U) => e.app U r)
  exact ConcreteCategory.bijective_of_isIso (e.app U)

/-- Equality transport retains the actual structure-sheaf unit. -/
theorem affineSource_unit_congr {Y Z : Scheme.{u}} {f g : Y ⟶ Z}
    (h : f = g) :
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
      (Scheme.Modules.pushforwardCongr h).hom.app
        (SheafOfModules.unit Y.ringCatSheaf) =
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  cases h
  apply Scheme.Modules.hom_ext (X := Z)
  intro U
  let O : Y.Modules := SheafOfModules.unit Y.ringCatSheaf
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let c := (Scheme.Modules.pushforwardCongr (rfl : f = f)).hom.app O
  have hc : c.app U = 𝟙 _ :=
    (Scheme.Modules.pushforwardCongr_hom_app_app (M := O) (rfl : f = f) U).trans
      (O.presheaf.map_id _)
  change Scheme.Modules.Hom.app (X := Z) q U ≫ c.app U = Scheme.Modules.Hom.app (X := Z) q U
  exact (congrArg (fun z => Scheme.Modules.Hom.app (X := Z) q U ≫ z) hc).trans (Category.comp_id (Scheme.Modules.Hom.app (X := Z) q U))

/-- Composition transport retains the actual structure-sheaf unit. -/
theorem affineSource_unit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app
          (SheafOfModules.unit X.ringCatSheaf) := by
  ext U
  rfl

/-- The actual pushforward from an affine source is transported to the
actual Spec coordinate map, using the canonical source isoSpec. -/
def affineSourcePushforwardUnitIso {R : CommRingCat.{u}}
    {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ Spec R) :
    (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      (Scheme.Modules.pushforward (Spec.map (affineSourceCoordinateMap f))).obj
        (SheafOfModules.unit (Spec Γ(Y, ⊤)).ringCatSheaf) := by
  let e := Y.isoSpec.hom
  let g := Spec.map (affineSourceCoordinateMap f)
  let q := SheafOfModules.unitToPushforwardObjUnit e.toRingCatSheafHom
  letI : IsIso q := affineSource_unit_isIso_of_isIso e
  exact (Scheme.Modules.pushforwardCongr (affineSourceCoordinateMap_spec f)).app _ ≪≫
    (Scheme.Modules.pushforwardComp e g).symm.app _ ≪≫
    (Scheme.Modules.pushforward g).mapIso (asIso q).symm

/-- The source transport preserves the original structure-sheaf inclusion,
not just the isomorphism class of its target. -/
theorem affineSourcePushforwardUnitIso_unit {R : CommRingCat.{u}}
    {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ Spec R) :
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
      (affineSourcePushforwardUnitIso f).hom =
    SheafOfModules.unitToPushforwardObjUnit
      (Spec.map (affineSourceCoordinateMap f)).toRingCatSheafHom := by
  let e := Y.isoSpec.hom
  let g := Spec.map (affineSourceCoordinateMap f)
  let q := SheafOfModules.unitToPushforwardObjUnit e.toRingCatSheafHom
  letI : IsIso q := affineSource_unit_isIso_of_isIso e
  have hc : SheafOfModules.unitToPushforwardObjUnit (e ≫ g).toRingCatSheafHom ≫
      (Scheme.Modules.pushforwardComp e g).inv.app
        (SheafOfModules.unit Y.ringCatSheaf) =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map q := by
    rw [affineSource_unit_comp]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact congrArg
      (fun z => SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫ z)
      (Category.comp_id ((Scheme.Modules.pushforward g).map q))
  change SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
    ((Scheme.Modules.pushforwardCongr (affineSourceCoordinateMap_spec f)).hom.app _ ≫
      (Scheme.Modules.pushforwardComp e g).inv.app _ ≫
      (Scheme.Modules.pushforward g).map (asIso q).inv) = _
  rw [← Category.assoc, ← Category.assoc, affineSource_unit_congr,
    hc, Category.assoc, ← Functor.map_comp]
  simp
  exact Category.comp_id
    (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom)

/-- For any actual affine source over Spec R, its actual pushforward
structure sheaf lies in the tilde essential image. No quasicoherence or
section-exactness certificate is supplied as a hypothesis. -/
theorem affineSourcePushforwardUnit_fromTildeGamma_isIso
    {R : CommRingCat.{u}} {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ Spec R) :
    IsIso (Scheme.Modules.fromTildeΓ (R := R)
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))) := by
  let N := (Scheme.Modules.pushforward (Spec.map (affineSourceCoordinateMap f))).obj
    (SheafOfModules.unit (Spec Γ(Y, ⊤)).ringCatSheaf)
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := Γ(Y, ⊤))
      (SheafOfModules.unit (Spec Γ(Y, ⊤)).ringCatSheaf)) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R) N) :=
    isIso_fromTildeΓ_pushforward (φ := affineSourceCoordinateMap f)
      (SheafOfModules.unit (Spec Γ(Y, ⊤)).ringCatSheaf)
  exact isIso_fromTildeΓ_iff.mpr
    ⟨(moduleSpecΓFunctor (R := R)).obj N,
      ⟨asIso (Scheme.Modules.fromTildeΓ (R := R) N) ≪≫
        (affineSourcePushforwardUnitIso f).symm⟩⟩

/-- Actual sections of the actual quotient SHEAF for an arbitrary affine
source over Spec R are the cokernel of the actual section inclusion. -/
def affineSourceQuotientSheaf_sectionsIso {R : CommRingCat.{u}}
    {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ Spec R) :
    (moduleSpecΓFunctor (R := R)).obj
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≅
    cokernel ((moduleSpecΓFunctor (R := R)).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := by
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R)
      (SheafOfModules.unit (Spec R).ringCatSheaf)) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R)
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))) :=
    affineSourcePushforwardUnit_fromTildeGamma_isIso f
  exact affineSheafCokernelSectionsIso (R := R)
    (M := SheafOfModules.unit (Spec R).ringCatSheaf)
    (N := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

/-- Actual quotient projections are preserved by the section comparison. -/
theorem affineSourceQuotientSheaf_sectionsIso_π {R : CommRingCat.{u}}
    {Y : Scheme.{u}} [IsAffine Y] (f : Y ⟶ Spec R) :
    (moduleSpecΓFunctor (R := R)).map
      (cokernel.π (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≫
        (affineSourceQuotientSheaf_sectionsIso f).hom =
      cokernel.π ((moduleSpecΓFunctor (R := R)).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) := by
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R)
      (SheafOfModules.unit (Spec R).ringCatSheaf)) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI : IsIso (Scheme.Modules.fromTildeΓ (R := R)
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))) :=
    affineSourcePushforwardUnit_fromTildeGamma_isIso f
  exact affineSheafCokernelSectionsIso_π (R := R)
    (M := SheafOfModules.unit (Spec R).ringCatSheaf)
    (N := (Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf))
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

end PfaffianDescent.Coray
