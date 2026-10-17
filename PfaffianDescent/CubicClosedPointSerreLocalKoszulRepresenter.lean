import PfaffianDescent.FieldPointKoszulGeneratorIdentification
import PfaffianDescent.SchemeModuleStalkMono

/-! # The canonical section representer becomes the actual unit on its open

The map represented by the section one sends the universal germ to one.
Its restriction to the represented open is therefore an isomorphism, with
the actual restriction/stalk comparison used to prove this assertion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

def cubicClosedPointSerreLocalKoszulRepresenterUnitMap
    {X : Scheme.{u}} (U : X.Opens) :
    (show X.Modules from sectionRepresenter X.ringCatSheaf U) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  sectionRepresenterAugmentation X.ringCatSheaf U
    (SheafOfModules.unit X.ringCatSheaf) (1 : Γ(X, U))

theorem cubicClosedPointSerreLocalKoszulRepresenterUnitMap_stalk_square
    {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U) :
    (sectionRepresenterStalkIso X U x hx).hom ≫
      (schemeModuleStalkModuleFunctor X x).map
        (cubicClosedPointSerreLocalKoszulRepresenterUnitMap U) ≫
      (schemeModuleUnitStalkIso X x).hom = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply (LinearMap.ringLmapEquivSelf (X.presheaf.stalk x) (X.presheaf.stalk x)
    (X.presheaf.stalk x)).injective
  change (schemeModuleUnitStalkIso X x).hom
    ((schemeModuleStalkModuleFunctor X x).map
      (cubicClosedPointSerreLocalKoszulRepresenterUnitMap U)
      ((sectionRepresenterStalkIso X U x hx).hom 1)) = 1
  rw [sectionRepresenterStalkIso_hom, sectionRepresenterStalkGeneratorHom_apply_one]
  rw [cubicClosedPointSerreLocalKoszulRepresenterUnitMap,
    sectionRepresenterAugmentation_stalk_generator]
  have h := schemeModuleSectionStalkCoordinateAddHom_unit U x hx (1 : Γ(X, U))
  change (schemeModuleUnitStalkIso X x).hom
      ((show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.germ
        U x hx (1 : Γ(X, U))) = _ at h
  simpa only [map_one] using h

theorem cubicClosedPointSerreLocalKoszulRepresenterUnitMap_stalk_isIso
    {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∈ U) :
    IsIso ((schemeModuleStalkModuleFunctor X x).map
      (cubicClosedPointSerreLocalKoszulRepresenterUnitMap U)) := by
  let e := sectionRepresenterStalkIso X U x hx
  let q := schemeModuleUnitStalkIso X x
  have hs : (schemeModuleStalkModuleFunctor X x).map
      (cubicClosedPointSerreLocalKoszulRepresenterUnitMap U) = e.inv ≫ q.inv := by
    apply (cancel_epi e.hom).mp
    apply (cancel_mono q.hom).mp
    simpa only [Category.assoc, e.hom_inv_id_assoc, q.inv_hom_id,
      Category.comp_id] using
      cubicClosedPointSerreLocalKoszulRepresenterUnitMap_stalk_square U x hx
  rw [hs]
  infer_instance

theorem cubicClosedPointSerreLocalKoszulRepresenterUnitMap_restrict_isIso
    {X : Scheme.{u}} (U : X.Opens) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (cubicClosedPointSerreLocalKoszulRepresenterUnitMap U)) := by
  apply schemeModuleMap_isIso_of_stalk
  intro x
  let a := cubicClosedPointSerreLocalKoszulRepresenterUnitMap U
  letI := cubicClosedPointSerreLocalKoszulRepresenterUnitMap_stalk_isIso U (U.ι x) x.2
  let G := forget₂ (ModuleCat (X.presheaf.stalk (U.ι x))) AddCommGrpCat
  have hglobal : IsIso ((schemeModuleStalkFunctor X (U.ι x)).map a) :=
    Functor.map_isIso G ((schemeModuleStalkModuleFunctor X (U.ι x)).map a)
  have hlocal : IsIso (((Scheme.Modules.restrictFunctor U.ι) ⋙
      schemeModuleStalkFunctor (U : Scheme) x).map a) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso U.ι x) a).mpr hglobal
  let H := forget₂ (ModuleCat ((U : Scheme).presheaf.stalk x)) AddCommGrpCat
  letI : IsIso (H.map ((schemeModuleStalkModuleFunctor (U : Scheme) x).map
      ((Scheme.Modules.restrictFunctor U.ι).map a))) := hlocal
  exact isIso_of_reflects_iso _ H

/-- The canonical unit coordinate on the actual restricted representer. -/
def cubicClosedPointSerreLocalKoszulRepresenterUnitIso
    {X : Scheme.{u}} (U : X.Opens) :
    (Scheme.Modules.restrictFunctor U.ι).obj
      (show X.Modules from sectionRepresenter X.ringCatSheaf U) ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf := by
  letI := cubicClosedPointSerreLocalKoszulRepresenterUnitMap_restrict_isIso U
  exact asIso ((Scheme.Modules.restrictFunctor U.ι).map
    (cubicClosedPointSerreLocalKoszulRepresenterUnitMap U)) ≪≫ Scheme.Modules.restrictUnitIso U.ι

end PfaffianDescent
