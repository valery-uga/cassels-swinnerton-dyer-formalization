import PfaffianDescent.SchemeModuleInternalHomDualOverUnit
import PfaffianDescent.SchemeModuleInternalHomIncrementExact
import PfaffianDescent.IdealSheafModule
import PfaffianDescent.SheafModulePushforwardExact
import Mathlib.CategoryTheory.Comma.Arrow

/-! Actual local cokernel comparison for the SAME canonical increment.
The entire GLOBAL cokernel is restricted to the actual over-site; exact
restriction and actual cokernel coforks are used, never an assertion that
sections commute with cokernels. A chart identifies this quotient with
the original closed-immersion unit pushforward. That identification
DEPENDS on the actual original ideal frame; it is not a canonical bare
residue-field identification. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.SchemeModuleInternalHom
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {M : X.Modules}

/-- The actual dual coefficient Iso carries the SAME canonical map to
the original inclusion preceded by the original chart inverse. -/
theorem unitToHom_overCoefficient
    (j : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (unitToHom j).over U ≫ (dualOverUnitIso U e).hom = e.inv ≫ j.over U := by
  apply SheafOfModules.hom_ext
  change ((unitToHom j).over U).val ≫ (dualOverUnitIso U e).hom.val =
    e.inv.val ≫ (j.over U).val
  rw [dualOverUnitIso_hom_val]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change Γ(X, V.unop.left) at r
  let frame := e.inv.val.app V (1 : Γ(X, V.unop.left))
  let E := evaluationBilinear M (SheafOfModules.unit X.ringCatSheaf) V.unop.left frame
  have hframe : e.inv.val.app V r = r • frame := by
    calc
      _ = e.inv.val.app V (r • (1 : Γ(X, V.unop.left))) := by
        rw [smul_eq_mul, mul_one]
      _ = r • frame := (e.inv.val.app V).hom.map_smul r (1 : Γ(X, V.unop.left))
  change E ((unitToHom j).val.app (op V.unop.left) r) =
    j.val.app (op V.unop.left) (e.inv.val.app V r)
  calc
    _ = E (r • homSection j V.unop.left) := rfl
    _ = r • E (homSection j V.unop.left) := E.map_smul r _
    _ = r • j.val.app (op V.unop.left) frame := rfl
    _ = j.val.app (op V.unop.left) (r • frame) :=
      ((j.val.app (op V.unop.left)).hom.map_smul r frame).symm
    _ = _ := congrArg (j.val.app (op V.unop.left)) hframe.symm

/-- The actual GLOBAL increment cokernel, restricted to U, is isomorphic
to the SAME original closed-immersion unit pushforward over U. All
exactness and cokernel conditions are derived internally. This Iso is
explicitly chosen-chart dependent. The intrinsic canonical fiber target
pushforward(pullback(actual dual)) is a separate remaining bridge. -/
def closedImmersionIncrement_cokernelOverIso
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule i).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (U : X.Opens)
    (e : (IdealSheafDataModule.closedImmersionModule i).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U) :
    (cokernel (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i))).over U ≅
      ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)).over U := by
  let F := SheafOfModules.overFunctor X.ringCatSheaf U
  letI : F.IsLeftAdjoint := by
    change (SheafOfModules.pushforward (𝟙 (X.ringCatSheaf.over U))).IsLeftAdjoint
    exact (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint
  letI : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint F
  let j := IdealSheafDataModule.closedImmersionModuleToUnit i
  letI : Mono j := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  let S := incrementCokernelSequence j
  let T := IdealSheafDataModule.closedImmersionModulePushforwardSequence i
  have hS : (S.map F).ShortExact :=
    SheafOfModules.ShortComplex.shortExact_map_overFunctor X.ringCatSheaf U S
      (incrementCokernelSequence_shortExact_of_pointwise_unitCharts j B hB eB)
  have hT : (T.map F).ShortExact :=
    SheafOfModules.ShortComplex.shortExact_map_overFunctor X.ringCatSheaf U T
      (IdealSheafDataModule.closedImmersionModulePushforwardSequence_shortExact i)
  let a : Arrow.mk ((S.map F).f) ≅ Arrow.mk ((T.map F).f) :=
    Arrow.isoMk e.symm (dualOverUnitIso U e) (unitToHom_overCoefficient j U e).symm
  exact CokernelCofork.mapIsoOfIsColimit hS.gIsCokernel hT.gIsCokernel a

/-- The chart cokernel Iso retains the ORIGINAL categorical projection
and ORIGINAL closed-immersion quotient map, with the actual dual-chart
coefficient on the middle term. No quotient-map certificate is an input. -/
theorem closedImmersionIncrement_cokernelOverIso_projection
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (B : X → X.Opens) (hB : ∀ x, x ∈ B x)
    (eB : ∀ x, (IdealSheafDataModule.closedImmersionModule i).over (B x) ≅
      (SheafOfModules.unit X.ringCatSheaf).over (B x))
    (U : X.Opens)
    (e : (IdealSheafDataModule.closedImmersionModule i).over U ≅
      (SheafOfModules.unit X.ringCatSheaf).over U) :
    (cokernel.π (unitToHom (IdealSheafDataModule.closedImmersionModuleToUnit i))).over U ≫
        (closedImmersionIncrement_cokernelOverIso i B hB eB U e).hom =
      (dualOverUnitIso U e).hom ≫
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i).over U := by
  letI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit i) := by
    change Mono (IdealSheafDataModule.idealModuleToUnit i.ker)
    infer_instance
  dsimp only [closedImmersionIncrement_cokernelOverIso,
    CokernelCofork.mapIsoOfIsColimit, CokernelCofork.mapOfIsColimit]
  exact (SheafOfModules.ShortComplex.shortExact_map_overFunctor X.ringCatSheaf U
    (incrementCokernelSequence (IdealSheafDataModule.closedImmersionModuleToUnit i))
    (incrementCokernelSequence_shortExact_of_pointwise_unitCharts
      (IdealSheafDataModule.closedImmersionModuleToUnit i) B hB eB)).gIsCokernel.fac
        _ WalkingParallelPair.one

end PfaffianDescent.SchemeModuleInternalHom
