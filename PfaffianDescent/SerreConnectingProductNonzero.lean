import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodNativeSerreData

/-! A compact name for the literal nonzero Serre connecting product.
This is a definition of the exact existing Ext condition, not an axiom. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
set_option backward.isDefEq.respectTransparency false

def SerreConnectingProductNonzero
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (T : X.Modules)
    [hExt : HasExt.{u} X.Modules]
    [PreservesFiniteLimits (schemeModuleTensorRight T)]
    [PreservesFiniteColimits (schemeModuleTensorRight T)]
    (e : SerreExtensionSequenceData X (closedImmersionIdealTwist i T)) : Prop :=
  letI : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hExt
  (closedImmersionIdealTwistSequence_shortExact i T).extClass.comp
    (@SerreExtensionSequenceData.extensionClass.{u} X _ e hExt)
      (show 1 + 1 = 2 by omega) ≠ 0

end PfaffianDescent
