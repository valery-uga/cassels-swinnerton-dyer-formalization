import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Detecting a nonzero point cohomology class by its ambient Cartier boundary

Only nonvanishing is needed here. An exact direct-image functor carries a
zero unit-source class to zero, while an injective ambient augmentation and
a nonzero Cartier boundary force that unit-source class to be nonzero.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w u' v' w'

set_option backward.isDefEq.respectTransparency false in
/-- A nonzero ambient Cartier boundary, detected by the actual augmentation,
forces the original point class to have a nonzero unit-source image. -/
theorem pointGlobalTraceCartier_unit_precomp_ne_zero
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [hExtC : HasExt.{w} C] [hExtD : HasExt.{w'} D]
    (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {U Q M : C} {V T : D}
    (γ : U ⟶ Q) (η : V ⟶ F.obj U) (a : V ⟶ F.obj Q)
    (hunit : η ≫ F.map γ = a)
    (z : Ext.{w} Q M 2) (β : Ext.{w'} (F.obj M) T 1)
    (hinj : Function.Injective
      ((Ext.mk₀.{w'} a).precomp T (zero_add 3)))
    (hboundary : (z.mapExactFunctor F).comp β rfl ≠ 0) :
    (Ext.mk₀.{w} γ).comp z (zero_add 2) ≠ 0 := by
  intro hz
  have hγ : (Ext.mk₀.{w'} (F.map γ)).comp (z.mapExactFunctor F) (zero_add 2) = 0 := by
    rw [← Ext.mapExactFunctor_mk₀, ← Ext.mapExactFunctor_comp,
      hz, Ext.mapExactFunctor_zero]
  have ha : (Ext.mk₀.{w'} a).comp (z.mapExactFunctor F) (zero_add 2) = 0 := by
    rw [← hunit, ← Ext.mk₀_comp_mk₀_assoc, hγ, Ext.comp_zero]
  have hwhole : (Ext.mk₀.{w'} a).comp
      ((z.mapExactFunctor F).comp β rfl) (zero_add 3) = 0 := by
    rw [← Ext.comp_assoc (Ext.mk₀.{w'} a) (z.mapExactFunctor F) β
      (zero_add 2) rfl (zero_add 3), ha, Ext.zero_comp]
  apply hboundary
  apply hinj
  change (Ext.mk₀.{w'} a).comp ((z.mapExactFunctor F).comp β rfl) (zero_add 3) =
    (Ext.mk₀.{w'} a).comp 0 (zero_add 3)
  simpa only [Ext.comp_zero] using hwhole

end PfaffianDescent
