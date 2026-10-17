import PfaffianDescent.CubicPointTraceFieldBaseChangeExtendedSupportScalar

/-! # Actual original residue scalars in native pulled-back Ext -/

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

/-- The proved original-scalar square in the inverse support coordinate. -/
theorem cubicPointTraceFieldBaseChangeExtendedSupportIso_scalar_inv (a : L) :
    cubicPointTraceFieldBaseChangeExtendedSupportOriginalScalar K L p i hi a ≫
      (cubicPointTraceFieldBaseChangeExtendedSupportIso K L p i hi).inv =
    (cubicPointTraceFieldBaseChangeExtendedSupportIso K L p i hi).inv ≫
      (Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeProjection K L p)).map
        (fieldPointPushforwardScalarEndomorphismAddHom i a) := by
  let e := cubicPointTraceFieldBaseChangeExtendedSupportIso K L p i hi
  change cubicPointTraceFieldBaseChangeExtendedSupportOriginalScalar K L p i hi a ≫
    e.inv = e.inv ≫ _
  apply (cancel_mono e.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [cubicPointTraceFieldBaseChangeExtendedSupportIso_scalar, Iso.inv_hom_id_assoc]

variable [HasExt.{u} X.Modules]
  [HasExt.{u} (schemeBaseChangeToField (L := L) X p).Modules]
  (N : X.Modules) (n : ℕ)

/-- Actual native pullback of a residue-scalar translate is precisely the
original tensor-factor translate on the actual extended point support. -/
theorem cubicPointTraceFieldBaseChangeExtendedSupportExtMap_scalar (a : L)
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) N n) :
    cubicPointTraceFieldBaseChangeExtendedSupportExtMap K L p i hi N n
        ((Ext.mk₀.{u} (C := X.Modules)
          (fieldPointPushforwardScalarEndomorphismAddHom i a)).comp z (zero_add n)) =
      (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
        (cubicPointTraceFieldBaseChangeExtendedSupportOriginalScalar K L p i hi a)).comp
        (cubicPointTraceFieldBaseChangeExtendedSupportExtMap K L p i hi N n z) (zero_add n) := by
  unfold cubicPointTraceFieldBaseChangeExtendedSupportExtMap
  rw [cubicPointTraceFieldBaseChangeFlatPullbackExtMap_precomp,
    Ext.mk₀_comp_mk₀_assoc,
    ← cubicPointTraceFieldBaseChangeExtendedSupportIso_scalar_inv,
    ← Ext.mk₀_comp_mk₀_assoc]

/-- If the original scalar translate has zero unit restriction, its actual
original-factor translate after field pullback has zero unit restriction. -/
theorem cubicPointTraceFieldBaseChangeExtendedSupportExtMap_scalar_unit_eq_zero (a : L)
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) N n)
    (hz : (Ext.mk₀.{u} (C := X.Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).comp
        ((Ext.mk₀.{u} (C := X.Modules)
          (fieldPointPushforwardScalarEndomorphismAddHom i a)).comp z (zero_add n))
        (zero_add n) = 0) :
    (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi))).comp
      ((Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
        (cubicPointTraceFieldBaseChangeExtendedSupportOriginalScalar K L p i hi a)).comp
        (cubicPointTraceFieldBaseChangeExtendedSupportExtMap K L p i hi N n z)
        (zero_add n)) (zero_add n) = 0 := by
  rw [← cubicPointTraceFieldBaseChangeExtendedSupportExtMap_scalar]
  exact cubicPointTraceFieldBaseChangeExtendedSupportExtMap_unit_eq_zero K L p i hi N n _ hz

end
end PfaffianDescent
