import PfaffianDescent.CubicPointTraceFieldBaseChangeProjectorScalars
import PfaffianDescent.CubicPointTraceFieldBaseChangeExtendedSupportScalarExt

/-! # Zero restriction descends to the actual diagonal point summand -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PfaffianDescent.BundleSectionZeroLocus
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (i : Spec (.of L) ⟶ X)
  (hi : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K L)))

/-- The actual new-base-field action on the entire extended point support. -/
def cubicPointTraceFieldBaseChangeExtendedSupportBaseScalar (b : L) :
    cubicPointTraceFieldBaseChangeExtendedPointPushforward K L p i hi ⟶
      cubicPointTraceFieldBaseChangeExtendedPointPushforward K L p i hi :=
  (Scheme.Modules.pushforward
    (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)).map
    (schemeModuleConstantEndomorphism
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom)) b)

/-- The new-field coefficient acts through the actual ambient unit
restriction, using the proved right-factor geometric projection. -/
theorem cubicPointTraceFieldBaseChangeExtendedSupportBaseScalar_unit (b : L) :
    IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi) ≫
      cubicPointTraceFieldBaseChangeExtendedSupportBaseScalar K L p i hi b =
    schemeModuleConstantEndomorphism
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) b ≫
      IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi) := by
  let j := cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi
  let q := pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  have h := cubicPointTraceFieldBaseChange_unitPushforward_regularFunction j
    (affineFunctionHom q b)
  change IdealSheafDataModule.closedImmersionUnitToPushforwardUnit j ≫
    (Scheme.Modules.pushforward j).map
      (schemeModuleConstantEndomorphism
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := L)).toRingHom)) b) =
    unitEndomorphismOfRegularFunction (affineFunctionHom q b) ≫ _
  rw [← cubicPointTraceFieldBaseChangeTensorPointToAmbient_toField K L p i hi,
    schemeModuleConstantEndomorphism, affineFunctionHom_comp]
  exact h.symm

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- The actual pushed-forward diagonal projector is the finite geometric
scalar expression, with actual source-field and new-field endomorphisms. -/
theorem cubicPointTraceFieldBaseChangePointSummandProjector_finite_scalars :
    ∃ s : Finset (L × L),
      cubicPointTraceFieldBaseChangePointSummandRestriction K L p i hi ≫
        cubicPointTraceFieldBaseChangePointSummandSection K L p i hi =
      ∑ ab ∈ s,
        cubicPointTraceFieldBaseChangeExtendedSupportBaseScalar K L p i hi ab.2 ≫
        cubicPointTraceFieldBaseChangeExtendedSupportOriginalScalar K L p i hi ab.1 := by
  obtain ⟨s, hs⟩ := cubicPointTraceFieldBaseChangeDiagonalSheafProjector_finite_scalars K L
  refine ⟨s, ?_⟩
  rw [cubicPointTraceFieldBaseChangePointSummandRestriction_section, hs, Functor.map_sum]
  apply Finset.sum_congr rfl
  intro ab hab
  exact (Scheme.Modules.pushforward
    (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)).map_comp _ _

variable [HasExt.{u} (schemeBaseChangeToField (L := L) X p).Modules]
  (N : (schemeBaseChangeToField (L := L) X p).Modules) (n : ℕ)

/-- If every actual original-field translate has zero unit restriction,
the actual diagonal-projector translate has zero unit restriction. -/
theorem cubicPointTraceFieldBaseChangePointSummandProjector_unit_eq_zero
    (w : Ext.{u} (cubicPointTraceFieldBaseChangeExtendedPointPushforward K L p i hi) N n)
    (hw : ∀ a : L,
      (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
        (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
          (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi))).comp
        ((Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
          (cubicPointTraceFieldBaseChangeExtendedSupportOriginalScalar K L p i hi a)).comp
          w (zero_add n)) (zero_add n) = 0) :
    (Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
      (IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
        (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi))).comp
      ((Ext.mk₀.{u} (C := (schemeBaseChangeToField (L := L) X p).Modules)
        (cubicPointTraceFieldBaseChangePointSummandRestriction K L p i hi ≫
          cubicPointTraceFieldBaseChangePointSummandSection K L p i hi)).comp
        w (zero_add n)) (zero_add n) = 0 := by
  classical
  let A := schemeBaseChangeToField (L := L) X p
  let M := cubicPointTraceFieldBaseChangeExtendedPointPushforward K L p i hi
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit
    (cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)
  let t : (M ⟶ M) →+ Ext.{u} (schemeModuleUnit A) N n := {
    toFun := fun v => (Ext.mk₀.{u} (C := A.Modules) q).comp
      ((Ext.mk₀.{u} (C := A.Modules) v).comp w (zero_add n)) (zero_add n)
    map_zero' := by rw [Ext.mk₀_zero, Ext.zero_comp, Ext.comp_zero]
    map_add' := fun v v' => by rw [Ext.mk₀_add, Ext.add_comp, Ext.comp_add] }
  obtain ⟨s, hs⟩ := cubicPointTraceFieldBaseChangePointSummandProjector_finite_scalars K L p i hi
  change t _ = 0
  rw [hs, map_sum]
  apply Finset.sum_eq_zero
  intro ab hab
  change (Ext.mk₀.{u} (C := A.Modules) q).comp
    ((Ext.mk₀.{u} (C := A.Modules)
      (cubicPointTraceFieldBaseChangeExtendedSupportBaseScalar K L p i hi ab.2 ≫
        cubicPointTraceFieldBaseChangeExtendedSupportOriginalScalar K L p i hi ab.1)).comp
      w (zero_add n)) (zero_add n) = 0
  rw [Ext.mk₀_comp_mk₀_assoc, ← Category.assoc,
    cubicPointTraceFieldBaseChangeExtendedSupportBaseScalar_unit,
    Category.assoc, ← Ext.mk₀_comp_mk₀_assoc,
    ← Ext.mk₀_comp_mk₀_assoc, hw ab.1, Ext.comp_zero]

end
end PfaffianDescent
