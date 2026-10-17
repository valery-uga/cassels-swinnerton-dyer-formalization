import PfaffianDescent.ActualP3IdealGlobalRestrictionKernel

/-! SOURCE ONLY / UNVERIFIED. Local tensor naturality reduces the ACTUAL
positive quotient restriction to the untwisted ACTUAL structure-sheaf map.
The next P3 task is to compute the coordinate defined here as p/X_j^m. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IdealSheafDataModule
universe u

/-- The true positive quotient restriction for an arbitrary twist. -/
def actualPositiveClosedImmersionRestriction
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (T : X.Modules) :=
  (schemeModuleTensorUnitLeftIso T).inv ≫ (closedImmersionIdealTwistSequence i T).g

/-- Local coordinate of a section, obtained from the SAME tensor
trivialization that acts on the actual quotient, without assuming a square. -/
def actualPositiveRestrictionLocalCoordinate
    {X : Scheme.{u}} (U : X.Opens) (T : X.Modules)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T) :=
  (Scheme.Modules.restrictFunctor U.ι).map s ≫
    (Scheme.Modules.restrictFunctor U.ι).map (schemeModuleTensorUnitLeftIso T).inv ≫
    (schemeModuleTensorRestrictIsoOfLocalTrivialization U
      (SheafOfModules.unit X.ringCatSheaf) T eT).hom

set_option backward.isDefEq.respectTransparency false in
/-- Genuine local kernel criterion. The map on the right is the actual
closed-immersion structure-sheaf augmentation; no ideal/evaluation comparison
certificate is assumed. -/
theorem actualPositiveRestriction_local_zero_iff
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (T : X.Modules)
    (eT : (SheafOfModules.overFunctor X.ringCatSheaf U).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf U)))
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T) :
    (Scheme.Modules.restrictFunctor U.ι).map
        (s ≫ actualPositiveClosedImmersionRestriction i T) = 0 ↔
      actualPositiveRestrictionLocalCoordinate U T eT s ≫
        (Scheme.Modules.restrictFunctor U.ι).map
          (closedImmersionUnitToPushforwardUnit i) = 0 := by
  let R := Scheme.Modules.restrictFunctor U.ι
  let Q := (Scheme.Modules.pushforward i).obj
    (SheafOfModules.unit Z.ringCatSheaf)
  let eQ := schemeModuleTensorRestrictIsoOfLocalTrivialization U Q T eT
  have hnat := schemeModuleTensorRestrictIsoOfLocalTrivialization_naturality
    U eT (closedImmersionUnitToPushforwardUnit i)
  have hsquare : R.map (s ≫ actualPositiveClosedImmersionRestriction i T) ≫ eQ.hom =
      actualPositiveRestrictionLocalCoordinate U T eT s ≫
        R.map (closedImmersionUnitToPushforwardUnit i) := by
    change R.map (s ≫ (schemeModuleTensorUnitLeftIso T).inv ≫
        schemeModuleTensorMap (closedImmersionUnitToPushforwardUnit i) (𝟙 T)) ≫
      eQ.hom = _
    rw [R.map_comp, R.map_comp]
    dsimp only [actualPositiveRestrictionLocalCoordinate]
    simp only [Category.assoc]
    rw [hnat]
  constructor
  · intro hs
    rw [← hsquare, hs, zero_comp]
  · intro hs
    apply (cancel_mono eQ.hom).mp
    rw [zero_comp, hsquare]
    exact hs

end PfaffianDescent
