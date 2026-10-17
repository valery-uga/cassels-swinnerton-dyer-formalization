import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! Actual restriction of pushforward structure modules for ANY scheme morphism.
No closed-immersion, base-change, or section-comparison certificate is assumed.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal open-restriction square identifies the actual pushforward
section ring with the actual section ring over the restricted morphism. -/
def openRestrictPushforwardUnit_sectionRingIso
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (W : U.toScheme.Opens) :
    Γ(Y, f ⁻¹ᵁ (U.ι ''ᵁ W)) ≅ Γ((f ⁻¹ᵁ U).toScheme, (f ∣_ U) ⁻¹ᵁ W) :=
  Y.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f U W)).op

/-- The actual section-ring comparison retains the ORIGINAL morphism app. -/
theorem openRestrictPushforwardUnit_sectionRingIso_comp_app
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) (W : U.toScheme.Opens) :
    f.app (U.ι ''ᵁ W) ≫ (openRestrictPushforwardUnit_sectionRingIso f U W).hom =
      (f ∣_ U).app W :=
  (morphismRestrict_app f U W).symm

/-- Restricting the ACTUAL pushed-forward structure module to an actual open
is the ACTUAL pushforward structure module of the restricted morphism. The
scalar compatibility and all component naturality are proved explicitly. -/
def openRestrictPushforwardUnitIso
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) ≅
    (Scheme.Modules.pushforward (f ∣_ U)).obj
      (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun W => ?_) ?_
  · let e := openRestrictPushforwardUnit_sectionRingIso f U W.unop
    refine ModuleCat.isoMk
      ((forget₂ CommRingCat RingCat ⋙ forget₂ _ Ab).mapIso e) ?_
    intro (r : Γ(U.toScheme, W.unop))
    ext (x : Γ(Y, f ⁻¹ᵁ (U.ι ''ᵁ W.unop)))
    change ((f ∣_ U).app W.unop r) * (e.hom x) =
      e.hom ((f.app (U.ι ''ᵁ W.unop) ((U.ι.appIso W.unop).inv r)) * x)
    have hr : e.hom (f.app (U.ι ''ᵁ W.unop) r) = (f ∣_ U).app W.unop r :=
      ConcreteCategory.congr_hom (openRestrictPushforwardUnit_sectionRingIso_comp_app f U W.unop) r
    have hι : (U.ι.appIso W.unop).inv.hom r = r := by
      rw [Scheme.Opens.ι_appIso] <;> rfl
    rw [hι, map_mul]
    exact (congrArg (fun z => z * e.hom x) hr).symm
  · intro W Z a
    let eW := openRestrictPushforwardUnit_sectionRingIso f U W.unop
    let eZ := openRestrictPushforwardUnit_sectionRingIso f U Z.unop
    have hnat :
        Y.presheaf.map (homOfLE (f.preimage_mono (U.ι.image_mono (leOfHom a.unop)))).op ≫
          eZ.hom =
        eW.hom ≫ Y.presheaf.map
          (homOfLE ((f ⁻¹ᵁ U).ι.image_mono ((f ∣_ U).preimage_mono (leOfHom a.unop)))).op := by
      dsimp only [eW, eZ, openRestrictPushforwardUnit_sectionRingIso, Functor.mapIso_hom,
        Iso.op_hom, eqToIso.hom]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
    ext x
    exact ConcreteCategory.congr_hom hnat x

/-- The comparison preserves the actual ORIGINAL structure-sheaf unit map.
Thus it compares the actual normalization quotient map, not just its objects. -/
theorem openRestrictPushforwardUnitIso_unit
    {Y X : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).map
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (openRestrictPushforwardUnitIso f U).hom =
      (Scheme.Modules.restrictUnitIso U.ι).hom ≫
        SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  let e := openRestrictPushforwardUnit_sectionRingIso f U W.unop
  have hComparison (x : Γ(Y, f ⁻¹ᵁ (U.ι ''ᵁ W.unop))) :
      ((openRestrictPushforwardUnitIso f U).hom.val.app W).hom x = e.hom.hom x := by
    change
      (((forget₂ RingCat Ab).map
        ((forget₂ CommRingCat RingCat).map
          (openRestrictPushforwardUnit_sectionRingIso f U W.unop).hom)).hom x) =
        e.hom.hom x
    rfl
  have hUnitRestriction (x : Γ(X, U.ι ''ᵁ W.unop)) :
      ((Scheme.Modules.restrictUnitIso U.ι).hom.val.app W).hom x =
        (U.ι.appIso W.unop).hom.hom x := by
    change
      (((forget₂ RingCat Ab).map
        ((forget₂ CommRingCat RingCat).map (U.ι.appIso W.unop).hom)).hom x) =
        (U.ι.appIso W.unop).hom.hom x
    rfl
  have hRestrictedMap :
      (((Scheme.Modules.restrictFunctor U.ι).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).val.app W).hom r =
      (f.app (U.ι ''ᵁ W.unop)).hom r := by
    rfl
  have hRestrictedUnit (x : Γ(U.toScheme, W.unop)) :
      ((SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom).val.app W).hom x =
      ((f ∣_ U).app W.unop).hom x := by
    rfl
  have hι : (U.ι.appIso W.unop).hom.hom r = r := by
    rw [Scheme.Opens.ι_appIso] <;> rfl
  have hcomp : e.hom.hom ((f.app (U.ι ''ᵁ W.unop)).hom r) =
      ((f ∣_ U).app W.unop).hom r :=
    ConcreteCategory.congr_hom
      (openRestrictPushforwardUnit_sectionRingIso_comp_app f U W.unop) r
  change
    ((openRestrictPushforwardUnitIso f U).hom.val.app W).hom
      ((((Scheme.Modules.restrictFunctor U.ι).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).val.app W).hom r) =
    ((SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom).val.app W).hom
      (((Scheme.Modules.restrictUnitIso U.ι).hom.val.app W).hom r)
  calc
    ((openRestrictPushforwardUnitIso f U).hom.val.app W).hom
        ((((Scheme.Modules.restrictFunctor U.ι).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).val.app W).hom r) =
        e.hom.hom ((f.app (U.ι ''ᵁ W.unop)).hom r) := by
      rw [hComparison, hRestrictedMap]
    _ = ((f ∣_ U).app W.unop).hom r := hcomp
    _ = ((SheafOfModules.unitToPushforwardObjUnit (f ∣_ U).toRingCatSheafHom).val.app W).hom
        (((Scheme.Modules.restrictUnitIso U.ι).hom.val.app W).hom r) := by
      rw [hRestrictedUnit, hUnitRestriction, hι]

end PfaffianDescent.Coray
