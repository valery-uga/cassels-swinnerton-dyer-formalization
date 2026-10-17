import PfaffianDescent.ExtMapFixedSource

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace PfaffianDescent
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem extPullback_postcomp {P Q Y Z : C} {n : ℕ}
    (g : P ⟶ Q) (a : Ext.{w} Q Y n) (h : Y ⟶ Z) :
    ((Ext.mk₀ g).comp a (zero_add n)).comp (Ext.mk₀ h) (add_zero n) =
      (Ext.mk₀ g).comp (a.comp (Ext.mk₀ h) (add_zero n)) (zero_add n) := by
  exact Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)

theorem extPrecompIsoOfIso_postcomp {X X' Y Z : C} {n : ℕ}
    (e : X ≅ X') (a : Ext.{w} X Y n) (h : Y ⟶ Z) :
    (extPrecompIsoOfIso e a).comp (Ext.mk₀ h) (add_zero n) =
      extPrecompIsoOfIso e (a.comp (Ext.mk₀ h) (add_zero n)) := by
  change ((Ext.mk₀ e.inv).comp a (zero_add n)).comp (Ext.mk₀ h) (add_zero n) =
    (Ext.mk₀ e.inv).comp (a.comp (Ext.mk₀ h) (add_zero n)) (zero_add n)
  exact Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)

end PfaffianDescent
