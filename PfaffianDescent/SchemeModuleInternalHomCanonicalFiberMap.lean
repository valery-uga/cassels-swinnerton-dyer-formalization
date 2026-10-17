import PfaffianDescent.SchemeModuleCanonicalFiberProjection
import PfaffianDescent.SchemeModuleInternalHomRankOneAction
import PfaffianDescent.SchemeModuleInternalHomIncrementExact

/-! The SAME canonical increment is killed by the ACTUAL adjunction
unit at its SAME constructed dual. Geometry/chart hypotheses derive
the dual evaluation Iso internally; the original closed-immersion
quotient relation then proves zero. The literal categorical cokernel
therefore has a CANONICAL map to the intrinsic pushed-forward fiber,
and the actual projection/fiber square is proved. Its invertibility
is a separate remaining theorem, not an input. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Z : Scheme.{u}}

/-- The original ideal's canonical increment is killed by the actual
intrinsic fiber map. Evaluation invertibility, action compatibility and
the zero relation are ALL derived internally; no flatness, comparison,
fiber exactness or point-increment certificate is assumed. -/
theorem closedImmersionDualIncrement_adjunctionUnit_zero
    (i : Z ⟶ X) [IsClosedImmersion i]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule i).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x)) :
    unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (dual (IdealSheafDataModule.closedImmersionModule i)) = 0 := by
  let M := (show X.Modules from IdealSheafDataModule.closedImmersionModule i)
  let D := dual M
  let j := IdealSheafDataModule.closedImmersionModuleToUnit i
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i
  let eta := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app D
  have hjq : j ≫ q = 0 := by
    have h := (IdealSheafDataModule.closedImmersionModulePushforwardSequence i).zero
    change j ≫ q = 0 at h
    exact h
  have ht : schemeModuleTensorMap j (𝟙 D) ≫ schemeModuleTensorMap q (𝟙 D) = 0 := by
    rw [schemeModuleTensorMap_comp, Category.id_comp, hjq]
    change (schemeModuleTensorRight D).map (0 : M ⟶ _) = 0
    exact (schemeModuleTensorRight D).map_zero _ _
  haveI : IsIso (dualEvaluation M) := dualEvaluation_isIso_of_pointwise_unitCharts M B hB eB
  apply (cancel_epi (dualEvaluation M)).mp
  calc
    dualEvaluation M ≫ (unitToHom j ≫ eta) = (dualEvaluation M ≫ unitToHom j) ≫ eta :=
      (Category.assoc _ _ _).symm
    _ = (schemeModuleTensorMap j (𝟙 D) ≫ (schemeModuleTensorUnitLeftIso D).hom) ≫ eta :=
      congrArg (fun f => f ≫ eta) (rankOneEvaluation_action_of_pointwise_unitCharts j B hB eB)
    _ = schemeModuleTensorMap j (𝟙 D) ≫ ((schemeModuleTensorUnitLeftIso D).hom ≫ eta) :=
      Category.assoc _ _ _
    _ = schemeModuleTensorMap j (𝟙 D) ≫
        (schemeModuleTensorMap q (𝟙 D) ≫ schemeModuleCanonicalFiberProjection i D) :=
      congrArg (schemeModuleTensorMap j (𝟙 D) ≫ ·)
        (schemeModuleCanonicalFiberProjection_unit_square i D).symm
    _ = (schemeModuleTensorMap j (𝟙 D) ≫ schemeModuleTensorMap q (𝟙 D)) ≫
        schemeModuleCanonicalFiberProjection i D := (Category.assoc _ _ _).symm
    _ = 0 ≫ schemeModuleCanonicalFiberProjection i D :=
      congrArg (· ≫ schemeModuleCanonicalFiberProjection i D) ht
    _ = 0 := zero_comp
    _ = dualEvaluation M ≫ 0 := comp_zero.symm

/-- The CANONICAL map from the SAME actual increment cokernel to the
actual intrinsic fiber. The map is the literal `cokernel.desc` of the
actual adjunction unit, not a chosen bare-residue comparison. -/
def closedImmersionDualIncrement_fiberMap
    (i : Z ⟶ X) [IsClosedImmersion i]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule i).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x)) :
    cokernel (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i)) ⟶
      (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj
        (dual (IdealSheafDataModule.closedImmersionModule i))) :=
  cokernel.desc (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i))
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (dual (IdealSheafDataModule.closedImmersionModule i)))
    (closedImmersionDualIncrement_adjunctionUnit_zero i B hB eB)

/-- The literal canonical cokernel projection followed by the actual
fiber factor is the SAME actual adjunction unit. -/
theorem closedImmersionDualIncrement_fiberMap_projection
    (i : Z ⟶ X) [IsClosedImmersion i]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule i).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x)) :
    cokernel.π (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i)) ≫
      closedImmersionDualIncrement_fiberMap i B hB eB =
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (dual (IdealSheafDataModule.closedImmersionModule i)) :=
  cokernel.π_desc _ _ _

/-- The FINAL canonical fiber factor is independent of every original
chart/generator choice used to prove zero. This is proved using its
actual projection square and the native epimorphic cokernel projection. -/
theorem closedImmersionDualIncrement_fiberMap_independent_charts
    (i : Z ⟶ X) [IsClosedImmersion i]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule i).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (B' : X → X.Opens) (hB' : ∀ x, x ∈ B' x)
    (eB' : ∀ x, (IdealSheafDataModule.closedImmersionModule i).over (B' x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B' x)) :
    closedImmersionDualIncrement_fiberMap i B hB eB =
      closedImmersionDualIncrement_fiberMap i B' hB' eB' := by
  apply (cancel_epi (cokernel.π
    (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i)))).mp
  exact (closedImmersionDualIncrement_fiberMap_projection i B hB eB).trans
    (closedImmersionDualIncrement_fiberMap_projection i B' hB' eB').symm

/-- Original pi-induced constants commute with the SAME actual canonical
fiber factor for its independently given original source/target module
actions. This does not invent an action on the point fiber. -/
theorem closedImmersionDualIncrement_fiberMap_originalBaseConstant
    {K : Type u} [Field K] (pi : X ⟶ Spec (CommRingCat.of K))
    (i : Z ⟶ X) [IsClosedImmersion i]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule i).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (U : X.Opens) (c : K)
    (z : (cokernel (unitToHom
      (IdealSheafDataModule.closedImmersionModuleToUnit i))).val.obj (op U)) :
    (closedImmersionDualIncrement_fiberMap i B hB eB).val.app (op U)
        (schemeOpenBaseRingHom pi U c • z) =
      schemeOpenBaseRingHom pi U c •
        (closedImmersionDualIncrement_fiberMap i B hB eB).val.app (op U) z :=
  ((closedImmersionDualIncrement_fiberMap i B hB eB).val.app (op U)).hom.map_smul _ _

end PfaffianDescent.SchemeModuleInternalHom
