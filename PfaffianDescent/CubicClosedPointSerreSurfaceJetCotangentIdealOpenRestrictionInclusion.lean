import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealOpenRestriction

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false

/-- The literal open-factor ideal isomorphism preserves the actual ideal inclusion. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso_toUnit
    {X U Z : Scheme.{u}} (f : U ⟶ X) [IsOpenImmersion f] (j : Z ⟶ U)
    [IsClosedImmersion j] [IsClosedImmersion (j ≫ f)] :
    (cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso f j).hom ≫
      closedImmersionModuleToUnit j =
    (Scheme.Modules.restrictFunctor f).map (closedImmersionModuleToUnit (j ≫ f)) ≫
      (Scheme.Modules.restrictUnitIso f).hom := by
  let R := Scheme.Modules.restrictFunctor f
  letI : PreservesFiniteLimits R := restrictFunctor_preservesFiniteLimits f
  let e := closedImmersionModuleToKernelIso j
  have he : e.inv ≫ closedImmersionModuleToUnit j =
      kernel.ι (closedImmersionUnitToPushforwardUnit j) := by
    rw [← closedImmersionModuleToKernel_comp j]
    exact e.inv_hom_id_assoc _
  unfold cubicClosedPointSerreSurfaceJetCotangent_idealOpenRestrictionIso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [he]
  change R.map (closedImmersionModuleToKernelIso (j ≫ f)).hom ≫
      (PreservesKernel.iso R (closedImmersionUnitToPushforwardUnit (j ≫ f))).hom ≫
      kernel.map _ _ (Scheme.Modules.restrictUnitIso f).hom
        (restrictPushforwardUnitFactorThroughOpenIso j f).hom
        (cubicClosedPointSerreSurfaceJetCotangent_closedQuotient_openRestriction f j) ≫
      kernel.ι (closedImmersionUnitToPushforwardUnit j) = _
  rw [kernel.lift_ι, PreservesKernel.iso_hom]
  have hk := kernelComparison_comp_ι
    (closedImmersionUnitToPushforwardUnit (j ≫ f)) R
  have hm := R.congr_map (closedImmersionModuleToKernel_comp (j ≫ f))
  rw [R.map_comp] at hm
  calc
    R.map (closedImmersionModuleToKernelIso (j ≫ f)).hom ≫
        kernelComparison (closedImmersionUnitToPushforwardUnit (j ≫ f)) R ≫
        kernel.ι (R.map (closedImmersionUnitToPushforwardUnit (j ≫ f))) ≫
        (Scheme.Modules.restrictUnitIso f).hom =
      (R.map (closedImmersionModuleToKernelIso (j ≫ f)).hom ≫
        R.map (kernel.ι (closedImmersionUnitToPushforwardUnit (j ≫ f)))) ≫
        (Scheme.Modules.restrictUnitIso f).hom := by
      rw [← Category.assoc (kernelComparison _ R), hk, ← Category.assoc]
    _ = _ := congrArg (fun t => t ≫ (Scheme.Modules.restrictUnitIso f).hom) hm

end PfaffianDescent
