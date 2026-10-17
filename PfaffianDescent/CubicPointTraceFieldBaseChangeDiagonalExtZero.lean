import PfaffianDescent.CubicPointTraceFieldBaseChangeProjectorZero

/-! # Actual zero descent to the residue-field rational point -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (i : Spec (.of L) ⟶ X)
  (hi : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K L)))
  [IsClosedImmersion i] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [HasExt.{u} X.Modules]
  [HasExt.{u} (schemeBaseChangeToField (L := L) X p).Modules]
  (N : X.Modules) (n : ℕ)

/-- Actual flat native Ext pullback followed by extraction of the constructed
diagonal rational-point summand. -/
def cubicPointTraceFieldBaseChangeDiagonalExtClass
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) N n) :
    Ext.{u} (cubicPointTraceFieldBaseChangeRationalPointPushforward K L p i hi)
      ((Scheme.Modules.pullback (cubicPointTraceFieldBaseChangeProjection K L p)).obj N) n :=
  (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
    (cubicPointTraceFieldBaseChangePointSummandSection K L p i hi)).comp
    (cubicPointTraceFieldBaseChangeExtendedSupportExtMap K L p i hi N n z) (zero_add n)

/-- Vanishing of the actual original unit restriction for every residue-field
translate forces vanishing of the actual diagonal rational-point restriction.
Every support, scalar, unit, and Ext pullback comparison in this descent is
constructed; no trace or cohomological base-change square is assumed. -/
theorem cubicPointTraceFieldBaseChangeDiagonalExtClass_unit_eq_zero
    (z : Ext.{u} ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit (Spec (.of L)).ringCatSheaf)) N n)
    (hz : ∀ a : L,
      (Ext.mk₀.{u} (C := X.Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit i)).comp
        ((Ext.mk₀.{u} (C := X.Modules)
          (fieldPointPushforwardScalarEndomorphismAddHom i a)).comp z (zero_add n))
        (zero_add n) = 0) :
    (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeRationalPoint K L p i hi))).comp
      (cubicPointTraceFieldBaseChangeDiagonalExtClass K L p i hi N n z) (zero_add n) = 0 := by
  rw [← cubicPointTraceFieldBaseChangePointSummandExtClass_unit K L p i hi]
  unfold cubicPointTraceFieldBaseChangeDiagonalExtClass
  rw [Ext.mk₀_comp_mk₀_assoc
    (cubicPointTraceFieldBaseChangePointSummandRestriction K L p i hi)
    (cubicPointTraceFieldBaseChangePointSummandSection K L p i hi)]
  apply cubicPointTraceFieldBaseChangePointSummandProjector_unit_eq_zero K L p i hi
  intro a
  exact cubicPointTraceFieldBaseChangeExtendedSupportExtMap_scalar_unit_eq_zero
    K L p i hi N n a z (hz a)

end
end PfaffianDescent
