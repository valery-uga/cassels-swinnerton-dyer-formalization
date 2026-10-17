import PfaffianDescent.CubicPointTraceFieldBaseChangeExtendedSupport

/-! # Native Ext transport to the actual extended point support -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (i : Spec (.of L) ⟶ X)
  (hi : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K L)))
  [IsClosedImmersion i]

/-- The unit square in the inverse direction used to transport Ext classes. -/
theorem cubicPointTraceFieldBaseChangeExtendedSupportIso_unit_inv :
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi) ≫
      (cubicPointTraceFieldBaseChangeExtendedSupportIso K L p i hi).inv =
    (cubicPointTraceFieldBaseChangePullbackUnitIso
      (cubicPointTraceFieldBaseChangeProjection K L p)).inv ≫
      (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeProjection K L p)).map
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i) := by
  let e := cubicPointTraceFieldBaseChangeExtendedSupportIso K L p i hi
  let u := cubicPointTraceFieldBaseChangePullbackUnitIso
    (cubicPointTraceFieldBaseChangeProjection K L p)
  change IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi) ≫ e.inv = u.inv ≫ _
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [cubicPointTraceFieldBaseChangeExtendedSupportIso_unit, Iso.inv_hom_id_assoc]

variable [HasExt.{u} X.Modules]
  [HasExt.{u} (schemeBaseChangeToField (L := L) X p).Modules]
  (N : X.Modules) (n : ℕ)

/-- Actual exact field pullback, transported to precisely the whole tensor
support used by the constructed rational-point summand. -/
def cubicPointTraceFieldBaseChangeExtendedSupportExtMap
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) N n) :
    Ext.{u} (cubicPointTraceFieldBaseChangeExtendedPointPushforward K L p i hi)
      ((Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeProjection K L p)).obj N) n :=
  (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
    (cubicPointTraceFieldBaseChangeExtendedSupportIso K L p i hi).inv).comp
    (cubicPointTraceFieldBaseChangeFlatPullbackExtMap
      (cubicPointTraceFieldBaseChangeProjection K L p) _ N n z) (zero_add n)

/-- Unit restriction of the actual tensor-support class is actual exact
pullback of the original unit restriction under the canonical unit coordinate. -/
theorem cubicPointTraceFieldBaseChangeExtendedSupportExtMap_unit
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) N n) :
    (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi))).comp
      (cubicPointTraceFieldBaseChangeExtendedSupportExtMap K L p i hi N n z) (zero_add n) =
    (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
      (cubicPointTraceFieldBaseChangePullbackUnitIso
        (cubicPointTraceFieldBaseChangeProjection K L p)).inv).comp
      (cubicPointTraceFieldBaseChangeFlatPullbackExtMap
        (cubicPointTraceFieldBaseChangeProjection K L p) _ N n
        ((Ext.mk₀.{u} (C := X.Modules)
          (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).comp z
            (zero_add n))) (zero_add n) := by
  unfold cubicPointTraceFieldBaseChangeExtendedSupportExtMap
  rw [Ext.mk₀_comp_mk₀_assoc,
    cubicPointTraceFieldBaseChangeExtendedSupportIso_unit_inv,
    ← Ext.mk₀_comp_mk₀_assoc,
    cubicPointTraceFieldBaseChangeFlatPullbackExtMap_precomp]

/-- A zero original unit restriction gives zero actual tensor-support unit
restriction, with every geometric identification proved. -/
theorem cubicPointTraceFieldBaseChangeExtendedSupportExtMap_unit_eq_zero
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) N n)
    (hz : (Ext.mk₀.{u} (C := X.Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).comp z
        (zero_add n) = 0) :
    (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi))).comp
      (cubicPointTraceFieldBaseChangeExtendedSupportExtMap K L p i hi N n z) (zero_add n) = 0 := by
  rw [cubicPointTraceFieldBaseChangeExtendedSupportExtMap_unit, hz, map_zero, Ext.comp_zero]

end
end PfaffianDescent
