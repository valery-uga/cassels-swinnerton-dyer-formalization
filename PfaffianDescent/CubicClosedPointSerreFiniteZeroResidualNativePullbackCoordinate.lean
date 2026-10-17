import PfaffianDescent.VoisinGenericPullbackCoordinates

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_native_pullback_coordinate
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : Type u) [Fintype I] [DecidableEq I]
    {M : Y.Modules} (e : SheafOfModules.free (R := Y.ringCatSheaf) I ≅ M)
    (s : M.sections) (i : I) :
    sectionCoordinateOfFreeIso I (pullbackFreeIso f I e)
      (pullbackSection f M (isIso_pullbackUnitComparison f) s) i =
      f.appTop (sectionCoordinateOfFreeIso I e s i) := by
  have h := moduleOpenTopLinearEquivOfPullbackFreeIso_general f I M e
    (schemeModuleSectionsEquivTop M s) i
  simp only [moduleOpenTopLinearEquivOfFreeIso_eq_freeSectionCoordinate,
    Equiv.symm_apply_apply] at h
  exact h

end PfaffianDescent
