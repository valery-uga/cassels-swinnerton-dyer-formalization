import PfaffianDescent.SchemeModuleInternalHomCanonicalFiberMap
import PfaffianDescent.SchemeModuleInternalHomIncrementChartCokernel

/-! The SAME GLOBAL increment cokernel is the actual tensor of the
original point-unit pushforward with the SAME constructed dual. The
dual's tensor exactness is derived from its genuine original-M charts,
and the actual evaluation and unit maps identify the first two terms.
The canonical fiber map factors through the SAME tensor quotient and
the actual projection-formula morphism. Its final Iso step is thereby
isolated precisely, not assumed. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Z : Scheme.{u}}

/-- Genuine GLOBAL tensor-quotient Iso of the SAME increment cokernel.
Dual evaluation invertibility and actual dual tensor exactness are
derived internally from original ideal charts, with no flatness or
quotient comparison certificate. -/
def closedImmersionDualIncrement_tensorCokernelIso
    (i : Z ⟶ X) [IsClosedImmersion i]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule i).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x)) :
    cokernel (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≅
      schemeModuleTensor ((Scheme.Modules.pushforward i).obj
        (SheafOfModules.unit Z.ringCatSheaf))
        (dual (IdealSheafDataModule.closedImmersionModule i)) := by
  let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
  let D := dual M
  let j := IdealSheafDataModule.closedImmersionModuleToUnit i
  let S := closedImmersionIdealTwistSequence i D
  let T := incrementCokernelSequence j
  have hcover : (Opens.grothendieckTopology X).CoversTop B := by
    apply (Opens.coversTop_iff X B).mpr
    apply top_unique
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x, hB x⟩
  have hS : S.ShortExact := closedImmersionIdealTwistSequence_shortExact_of_coversTop_iso_unit
    i B hcover (fun x => dualOverUnitIso (B x) (eB x) ≪≫ unitOverIso (B x))
  letI : Mono j := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  have hT : T.ShortExact := incrementCokernelSequence_shortExact_of_pointwise_unitCharts j B hB eB
  haveI : IsIso (dualEvaluation M) := dualEvaluation_isIso_of_pointwise_unitCharts M B hB eB
  let a : Arrow.mk S.f ≅ Arrow.mk T.f := Arrow.isoMk
    (asIso (dualEvaluation M)) (schemeModuleTensorUnitLeftIso D)
    (rankOneEvaluation_action_of_pointwise_unitCharts j B hB eB)
  exact (CokernelCofork.mapIsoOfIsColimit hS.gIsCokernel hT.gIsCokernel a).symm

/-- The genuine tensor-cokernel Iso retains the SAME original πδ and
the SAME original residue restriction q, with the actual unit-left
inverse on D. No quotient-projection square is an input. -/
theorem closedImmersionDualIncrement_tensorCokernelIso_projection
    (i : Z ⟶ X) [IsClosedImmersion i]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule i).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x)) :
    cokernel.π (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≫
        (closedImmersionDualIncrement_tensorCokernelIso i B hB eB).hom =
      (schemeModuleTensorUnitLeftIso (dual (IdealSheafDataModule.closedImmersionModule i))).inv ≫
        schemeModuleTensorMap (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)
          (𝟙 (dual (IdealSheafDataModule.closedImmersionModule i))) := by
  let D := dual (IdealSheafDataModule.closedImmersionModule i)
  let E := closedImmersionDualIncrement_tensorCokernelIso i B hB eB
  let L := schemeModuleTensorUnitLeftIso D
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let pi := cokernel.π (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i))
  have h : schemeModuleTensorMap q (𝟙 D) ≫ E.inv = L.hom ≫ pi := by
    dsimp only [E, closedImmersionDualIncrement_tensorCokernelIso,
      Iso.symm_inv, CokernelCofork.mapIsoOfIsColimit, CokernelCofork.mapOfIsColimit]
    exact (closedImmersionIdealTwistSequence_shortExact_of_coversTop_iso_unit
      i B ((Opens.coversTop_iff X B).mpr (by
        apply top_unique
        intro x hx
        exact Opens.mem_iSup.mpr ⟨x, hB x⟩))
      (fun x => dualOverUnitIso (B x) (eB x) ≪≫ unitOverIso (B x))).gIsCokernel.fac
        _ WalkingParallelPair.one
  apply L.eq_inv_comp.mpr
  exact (Category.assoc L.hom pi E.hom).symm.trans (E.comp_inv_eq.mp h).symm

/-- The CANONICAL map to the intrinsic fiber is precisely the actual
GLOBAL tensor-cokernel Iso followed by the SAME canonical projection-
formula morphism. Hence no arbitrary chart comparison is substituted. -/
theorem closedImmersionDualIncrement_fiberMap_eq_tensorProjection
    (i : Z ⟶ X) [IsClosedImmersion i]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule i).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x)) :
    closedImmersionDualIncrement_fiberMap i B hB eB =
      (closedImmersionDualIncrement_tensorCokernelIso i B hB eB).hom ≫
        schemeModuleCanonicalFiberProjection i
          (dual (IdealSheafDataModule.closedImmersionModule i)) := by
  apply (cancel_epi (cokernel.π
    (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i)))).mp
  rw [closedImmersionDualIncrement_fiberMap_projection, ← Category.assoc,
    closedImmersionDualIncrement_tensorCokernelIso_projection, Category.assoc,
    schemeModuleCanonicalFiberProjection_unit_square]
  exact (Iso.inv_hom_id_assoc _ _).symm

/-- The precise remaining intrinsic-Iso obligation is invertibility of
the ACTUAL canonical projection-formula morphism, not an arbitrary
comparison. This equivalence follows from the genuine tensor-cokernel
Iso already proved. It does not assume either side in a primitive caller. -/
theorem closedImmersionDualIncrement_fiberMap_isIso_iff_tensorProjection
    (i : Z ⟶ X) [IsClosedImmersion i]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule i).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x)) :
    IsIso (closedImmersionDualIncrement_fiberMap i B hB eB) ↔
      IsIso (schemeModuleCanonicalFiberProjection i
        (dual (IdealSheafDataModule.closedImmersionModule i))) := by
  let E := closedImmersionDualIncrement_tensorCokernelIso i B hB eB
  let f := schemeModuleCanonicalFiberProjection i
    (dual (IdealSheafDataModule.closedImmersionModule i))
  constructor
  · intro h
    letI := h
    haveI : IsIso (E.hom ≫ f) := by
      rw [← closedImmersionDualIncrement_fiberMap_eq_tensorProjection i B hB eB]
      infer_instance
    exact IsIso.of_isIso_comp_left E.hom f
  · intro h
    letI := h
    rw [closedImmersionDualIncrement_fiberMap_eq_tensorProjection i B hB eB]
    infer_instance

end PfaffianDescent.SchemeModuleInternalHom
