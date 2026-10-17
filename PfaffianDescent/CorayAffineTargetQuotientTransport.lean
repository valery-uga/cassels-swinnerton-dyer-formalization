import PfaffianDescent.CorayAffineSourceSpecTransport
import Mathlib.CategoryTheory.Adjunction.Limits

/-! Actual quotient-sheaf transport across a canonical affine target.
STATUS: UNVERIFIED source only. Root owns all compiler checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The ACTUAL pushforward along a scheme isomorphism is an equivalence,
using only actual composition, equality and identity pushforward isomorphisms. -/
def schemeIsoPushforwardEquivalence {X Z : Scheme.{u}} (e : X ≅ Z) :
    X.Modules ≌ Z.Modules := by
  let F := Scheme.Modules.pushforward e.hom
  let G := Scheme.Modules.pushforward e.inv
  let η : 𝟭 X.Modules ≅ F ⋙ G :=
    (Scheme.Modules.pushforwardId X).symm ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).symm ≪≫
      (Scheme.Modules.pushforwardComp e.hom e.inv).symm
  let ε : G ⋙ F ≅ 𝟭 Z.Modules :=
    Scheme.Modules.pushforwardComp e.inv e.hom ≪≫
      Scheme.Modules.pushforwardCongr e.inv_hom_id ≪≫
      Scheme.Modules.pushforwardId Z
  letI : F.IsEquivalence := Functor.IsEquivalence.mk' G η ε
  exact F.asEquivalence

/-- The equivalence uses the actual pushforward, not a replacement functor. -/
theorem schemeIsoPushforwardEquivalence_functor {X Z : Scheme.{u}} (e : X ≅ Z) :
    (schemeIsoPushforwardEquivalence e).functor = Scheme.Modules.pushforward e.hom := rfl

/-- Target transport identifies the actual sheaf cokernel of O_X -> f_*O_Y
with the actual cokernel for f followed by the scheme isomorphism. -/
def schemeIsoTargetQuotientSheafIso {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (e : X ≅ Z) :
    (Scheme.Modules.pushforward e.hom).obj
      (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≅
    cokernel (SheafOfModules.unitToPushforwardObjUnit (f ≫ e.hom).toRingCatSheafHom) := by
  let F := Scheme.Modules.pushforward e.hom
  letI : F.IsEquivalence := (schemeIsoPushforwardEquivalence e).isEquivalence_functor
  let qf := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let qe := SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom
  letI : IsIso qe := affineSource_unit_isIso_of_isIso e.hom
  let eA := (asIso qe).symm
  let eB := (Scheme.Modules.pushforwardComp f e.hom).app
    (SheafOfModules.unit Y.ringCatSheaf)
  have hc : F.map qf ≫ eB.hom = eA.hom ≫
      SheafOfModules.unitToPushforwardObjUnit (f ≫ e.hom).toRingCatSheafHom := by
    rw [affineSource_unit_comp]
    change F.map qf ≫ eB.hom = (asIso qe).inv ≫ qe ≫ F.map qf ≫ eB.hom
    exact ((asIso qe).inv_hom_id_assoc (F.map qf ≫ eB.hom)).symm
  exact PreservesCokernel.iso F qf ≪≫
    cokernel.mapIso (F.map qf)
      (SheafOfModules.unitToPushforwardObjUnit (f ≫ e.hom).toRingCatSheafHom) eA eB hc

/-- Target transport preserves the actual quotient projection. -/
theorem schemeIsoTargetQuotientSheafIso_π {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (e : X ≅ Z) :
    (Scheme.Modules.pushforward e.hom).map
      (cokernel.π (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≫
        (schemeIsoTargetQuotientSheafIso f e).hom =
      (Scheme.Modules.pushforwardComp f e.hom).hom.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      cokernel.π
        (SheafOfModules.unitToPushforwardObjUnit (f ≫ e.hom).toRingCatSheafHom) := by
  let F := Scheme.Modules.pushforward e.hom
  letI : F.IsEquivalence := (schemeIsoPushforwardEquivalence e).isEquivalence_functor
  let qe := SheafOfModules.unitToPushforwardObjUnit e.hom.toRingCatSheafHom
  letI : IsIso qe := affineSource_unit_isIso_of_isIso e.hom
  dsimp only [schemeIsoTargetQuotientSheafIso, Iso.trans_hom]
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

/-- For actual affine source and target, the actual quotient sheaf,
transported through the target's CANONICAL isoSpec, has sections given by
the actual section cokernel. Both geometric affineness hypotheses are primitive. -/
def affineTargetQuotientSheaf_specSectionsIso {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X) :
    (moduleSpecΓFunctor (R := Γ(X, ⊤))).obj
      ((Scheme.Modules.pushforward X.isoSpec.hom).obj
        (cokernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))) ≅
    cokernel ((moduleSpecΓFunctor (R := Γ(X, ⊤))).map
      (SheafOfModules.unitToPushforwardObjUnit (f ≫ X.isoSpec.hom).toRingCatSheafHom)) :=
  (moduleSpecΓFunctor (R := Γ(X, ⊤))).mapIso
    (schemeIsoTargetQuotientSheafIso f X.isoSpec) ≪≫
    affineSourceQuotientSheaf_sectionsIso (f ≫ X.isoSpec.hom)

/-- The canonical affine-target section comparison preserves the actual
quotient projection, including the actual pushforward-composition map. -/
theorem affineTargetQuotientSheaf_specSectionsIso_π {X Y : Scheme.{u}}
    [IsAffine X] [IsAffine Y] (f : Y ⟶ X) :
    (moduleSpecΓFunctor (R := Γ(X, ⊤))).map
      ((Scheme.Modules.pushforward X.isoSpec.hom).map
        (cokernel.π (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom))) ≫
      (affineTargetQuotientSheaf_specSectionsIso f).hom =
    (moduleSpecΓFunctor (R := Γ(X, ⊤))).map
      ((Scheme.Modules.pushforwardComp f X.isoSpec.hom).hom.app
        (SheafOfModules.unit Y.ringCatSheaf)) ≫
    cokernel.π ((moduleSpecΓFunctor (R := Γ(X, ⊤))).map
      (SheafOfModules.unitToPushforwardObjUnit (f ≫ X.isoSpec.hom).toRingCatSheafHom)) := by
  dsimp only [affineTargetQuotientSheaf_specSectionsIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, schemeIsoTargetQuotientSheafIso_π,
    Functor.map_comp, Category.assoc, affineSourceQuotientSheaf_sectionsIso_π]

end PfaffianDescent.Coray
