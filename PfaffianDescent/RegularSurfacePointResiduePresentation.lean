import PfaffianDescent.FieldPointLocalTargetResiduePresentation
import PfaffianDescent.RegularSurfacePointTargetExtCoordinate

/-! # Residue presentations retained by regular-surface coordinate construction -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
namespace PfaffianDescent
universe u

set_option backward.isDefEq.respectTransparency false in
/-- The internally chosen affine chart and parameters realize the actual constructed
regular-surface point coordinate as a literal local residue coordinate. -/
theorem fieldPointExtTwoCoordinateAddEquivOfRegularSurfacePointLocalTarget_residuePresentation
    {L : Type u} [Field L] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (i : Spec (.of L) ⟶ X) [IsClosedImmersion i]
    [IsRegularLocalRing (X.presheaf.stalk (i default))]
    (hdim : ringKrullDim (X.presheaf.stalk (i default)) = 2)
    (T : X.Modules) {J : Type u} (V : J → X.Opens)
    (hV : (Opens.grothendieckTopology X).CoversTop V)
    (eV : ∀ j, (SheafOfModules.overFunctor X.ringCatSheaf (V j)).obj T ≅
      SheafOfModules.unit (SheafOfModules.commRingSheafToRingSheaf
        (SheafOfModules.commRingSheafOver X.sheaf (V j))))
    (Y : X.Modules)
    (eYV : ∀ j, Y.restrict (V j).ι ≅ SheafOfModules.unit (V j : Scheme).ringCatSheaf)
    [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk (i default)))] :
    Nonempty (FieldPointExtResiduePresentation i default
      (closedImmersionIdealTwistSequence i T).X₃ Y
      (fieldPointExtTwoCoordinateAddEquivOfRegularSurfacePointLocalTarget
        i hdim T V hV eV Y eYV)) := by
  exact ⟨(regularSurfacePointExtCoordinateWithResiduePresentation
    i hdim T V hV eV Y eYV).2⟩

end PfaffianDescent
