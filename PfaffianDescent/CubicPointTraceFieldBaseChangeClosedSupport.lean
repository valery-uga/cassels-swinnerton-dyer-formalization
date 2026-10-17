import PfaffianDescent.CubicPointTraceFieldBaseChangeFlatExt
import PfaffianDescent.AffineSourceChartBaseChange

/-! # Actual point-support transport under flat base change

The support identification is the actual closed-immersion pushforward
base-change map. Its quotient square is proved, and transports native Ext
unit-precomposition without assuming a cohomological base-change square.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual pulled-back structure modules identify by the canonical
unit comparison. -/
def cubicPointTraceFieldBaseChangePullbackUnitIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  letI := BundleSectionZeroLocus.isIso_pullbackUnitComparison f
  exact asIso (BundleSectionZeroLocus.pullbackUnitComparison f)

/-- The actual pulled-back closed-point support identifies with the actual
pushforward from its scheme-theoretic fibre product. -/
def cubicPointTraceFieldBaseChangeClosedSupportIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y) [IsClosedImmersion i] :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) ≅
    (Scheme.Modules.pushforward (pullback.fst f i)).obj
      (SheafOfModules.unit (pullback f i).ringCatSheaf) := by
  letI := isIso_closedImmersionPushforwardBaseChangeHom_general f i
  exact asIso (closedImmersionPushforwardBaseChangeHom f i)

/-- The actual source-unit quotient square, expressed in the direction used
to transport Ext classes from the original point to the extended support. -/
theorem cubicPointTraceFieldBaseChangeClosedSupportIso_unit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y) [IsClosedImmersion i] :
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit (pullback.fst f i) ≫
        (cubicPointTraceFieldBaseChangeClosedSupportIso f i).inv =
      (cubicPointTraceFieldBaseChangePullbackUnitIso f).inv ≫
        (Scheme.Modules.pullback f).map
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) := by
  let e := cubicPointTraceFieldBaseChangeClosedSupportIso f i
  let u := cubicPointTraceFieldBaseChangePullbackUnitIso f
  have h : (Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) ≫ e.hom =
    u.hom ≫ IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
      (pullback.fst f i) := closedImmersionPushforwardBaseChangeHom_quotient f i
  change IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (pullback.fst f i) ≫ e.inv = u.inv ≫ _
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h, Iso.inv_hom_id_assoc]

section
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) [Flat f]
  (i : Z ⟶ Y) [IsClosedImmersion i]
  [HasExt.{u} Y.Modules] [HasExt.{u} X.Modules]
  (N : Y.Modules) (n : ℕ)

/-- Actual native Ext pullback followed by the proved actual support
identification. -/
def cubicPointTraceFieldBaseChangeClosedSupportExtMap
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) N n) :
    Ext.{u} ((Scheme.Modules.pushforward (pullback.fst f i)).obj
      (SheafOfModules.unit (pullback f i).ringCatSheaf))
      ((Scheme.Modules.pullback f).obj N) n :=
  (Ext.mk₀.{u} (C := X.Modules)
    (cubicPointTraceFieldBaseChangeClosedSupportIso f i).inv).comp
      (cubicPointTraceFieldBaseChangeFlatPullbackExtMap f _ N n z) (zero_add n)

/-- The actual unit restriction of the transported point class is precisely
the transported original unit restriction. -/
theorem cubicPointTraceFieldBaseChangeClosedSupportExtMap_unit
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) N n) :
    (Ext.mk₀.{u} (C := X.Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (pullback.fst f i))).comp
      (cubicPointTraceFieldBaseChangeClosedSupportExtMap f i N n z) (zero_add n) =
    (Ext.mk₀.{u} (C := X.Modules)
      (cubicPointTraceFieldBaseChangePullbackUnitIso f).inv).comp
      (cubicPointTraceFieldBaseChangeFlatPullbackExtMap f _ N n
        ((Ext.mk₀.{u} (C := Y.Modules)
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).comp
            z (zero_add n))) (zero_add n) := by
  unfold cubicPointTraceFieldBaseChangeClosedSupportExtMap
  rw [Ext.mk₀_comp_mk₀_assoc,
    cubicPointTraceFieldBaseChangeClosedSupportIso_unit,
    ← Ext.mk₀_comp_mk₀_assoc,
    cubicPointTraceFieldBaseChangeFlatPullbackExtMap_precomp]

/-- Zero original unit restriction gives zero actual extended-support unit
restriction, using only exact geometric pullback and the proved quotient square. -/
theorem cubicPointTraceFieldBaseChangeClosedSupportExtMap_unit_eq_zero
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)) N n)
    (hz : (Ext.mk₀.{u} (C := Y.Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).comp z
        (zero_add n) = 0) :
    (Ext.mk₀.{u} (C := X.Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (pullback.fst f i))).comp
      (cubicPointTraceFieldBaseChangeClosedSupportExtMap f i N n z) (zero_add n) = 0 := by
  rw [cubicPointTraceFieldBaseChangeClosedSupportExtMap_unit, hz, map_zero, Ext.comp_zero]

end
end PfaffianDescent
