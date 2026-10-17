import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! Bounded Yoneda assembly for the actual coefficient Iso followed by
an exact native functor and a WHOLE sequence Iso. No class square is input. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u u' v v' w w'
set_option backward.isDefEq.respectTransparency false

lemma exactFunctor_coefficientIso_cancel206
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {M N N' : C} (z : Ext.{w} M N 2) (e : N ≅ N')
    {P : D} (b : F.obj N ⟶ P) :
    ((z.comp (Ext.mk₀ e.hom) (add_zero 2)).mapExactFunctor F).comp
      (Ext.mk₀ (F.map e.inv ≫ b)) (add_zero 2) =
      (z.mapExactFunctor F).comp (Ext.mk₀ b) (add_zero 2) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
    ← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp]

/-- The coefficient renumbering Iso is retained, then cancelled through
its actual inverse. The WHOLE sequence Iso derives the resulting boundary
identity by actual ShortExact class naturality. -/
theorem exactBoundary_coefficientIso_nativeSequence206
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : ShortComplex C) (hS : S.ShortExact)
    (T : ShortComplex D) (hT : T.ShortExact) (a : S.map F ≅ T)
    (N : C) (e : S.X₁ ≅ N) (M : C) (r : Ext.{w} M S.X₃ 1) :
    (((r.comp hS.extClass rfl).comp (Ext.mk₀ e.hom) (add_zero 2)).mapExactFunctor F).comp
      (Ext.mk₀ (F.map e.inv ≫ a.hom.τ₁)) (add_zero 2) =
      ((r.mapExactFunctor F).comp (Ext.mk₀ a.hom.τ₃) (add_zero 1)).comp
        hT.extClass rfl := by
  rw [exactFunctor_coefficientIso_cancel206, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass, Ext.comp_assoc_of_third_deg_zero,
    (hS.map_of_exact F).extClass_naturality hT a.hom,
    ← Ext.comp_assoc_of_second_deg_zero]

end PfaffianDescent
