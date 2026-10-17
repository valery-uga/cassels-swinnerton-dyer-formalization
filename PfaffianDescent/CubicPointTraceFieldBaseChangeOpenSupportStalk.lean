import PfaffianDescent.VoisinHypersurfaceCokernel
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-! # Actual unit restriction is invertible on an open support stalk -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- At a source point of an open immersion, the actual unit-to-pushforward
map induces an isomorphism on the actual module stalk. -/
theorem cubicPointTraceFieldBaseChangeOpenSupportUnitStalk_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    IsIso ((schemeModuleStalkModuleFunctor Y (f x)).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f)) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit f
  let φ := schemeModuleStalkLinearMap q (f x)
  let eY := presheafOfModules_unitStalkLinearEquiv Y.presheaf (f x)
  let eX := presheafOfModules_unitStalkLinearEquiv X.presheaf x
  let push := TopCat.Presheaf.stalkPushforward AddCommGrpCat f.base
    (SheafOfModules.unit X.ringCatSheaf).val.presheaf x
  letI : IsIso push :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat f.isOpenEmbedding.isInducing
      (SheafOfModules.unit X.ringCatSheaf).val.presheaf x
  have hpush := ConcreteCategory.bijective_of_isIso push
  have hf := ConcreteCategory.bijective_of_isIso (f.stalkMap x)
  have h (r : Y.presheaf.stalk (f x)) :
      eX.symm (push (φ (eY r))) = f.stalkMap x r :=
    closedImmersionPushforwardStalkFromRingLinearMap_comp_stalkPushforward f x r
  change Function.Bijective φ
  constructor
  · intro r s hrs
    apply eY.symm.injective
    apply hf.injective
    rw [← h, ← h, eY.apply_symm_apply, eY.apply_symm_apply, hrs]
  · intro z
    obtain ⟨r, hr⟩ := hf.surjective (eX.symm (push z))
    refine ⟨eY r, ?_⟩
    apply hpush.injective
    apply eX.symm.injective
    exact (h r).trans hr

end PfaffianDescent
