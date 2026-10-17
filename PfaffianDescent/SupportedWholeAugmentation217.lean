import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! Honest endpoint pullback of an unchanged supported class. The
coefficient-one coordinate is constructed from the actual whole quotient. -/
noncomputable section
set_option autoImplicit false
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u v w

/-- The actual whole-quotient coordinate constructs this augmentation. -/
def supportedWholeCoefficientOneAugmentation217
    {C : Type u} [Category.{v} C] {T N M : C} (K : T ≅ N) (kappa : M ⟶ N) :
    M ⟶ T := kappa ≫ K.inv

lemma supportedWholeCoefficientOneAugmentation_comp217
    {C : Type u} [Category.{v} C] {T N M : C} (K : T ≅ N) (kappa : M ⟶ N) :
    supportedWholeCoefficientOneAugmentation217 K kappa ≫ K.hom = kappa := by
  simp only [supportedWholeCoefficientOneAugmentation217, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/--213's derived source square identifies the constructed coefficient-one
coordinate with the canonical augmentation followed by its actual inverse
unit automorphism. This generic cancellation has no Ext-class hypothesis. -/
lemma supportedWholeCoefficientOneAugmentation_unitFactor217
    {C : Type u} [Category.{v} C] {T N M : C} (K : T ≅ N) (kappa : M ⟶ N)
    (lambda : M ⟶ T) (mu : N ≅ N)
    (h : lambda ≫ K.hom = kappa ≫ mu.hom) :
    supportedWholeCoefficientOneAugmentation217 K kappa =
      lambda ≫ K.hom ≫ mu.inv ≫ K.inv := by
  rw [← Category.assoc, ← Category.assoc, h]
  simp only [supportedWholeCoefficientOneAugmentation217, Category.assoc,
    Iso.hom_inv_id_assoc]

/-- Pulling back the SAME supported class through this constructed endpoint
recovers the SAME whole extension and its target coordinate. -/
lemma supportedWholeFirstCartier_pullback217
    {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    {T N M B Q O : C} (K : T ≅ N) (kappa : M ⟶ N)
    (alpha : Ext.{w} N B 1) (b : B ⟶ Q) (delta : Ext.{w} Q O 1) :
    (Ext.mk₀ (supportedWholeCoefficientOneAugmentation217 K kappa)).comp
      (((Ext.mk₀ K.hom).comp (alpha.comp (Ext.mk₀ b) (add_zero 1))
        (zero_add 1)).comp delta rfl) (zero_add 2) =
      ((Ext.mk₀ kappa).comp (alpha.comp (Ext.mk₀ b) (add_zero 1))
        (zero_add 1)).comp delta rfl := by
  have hAssoc := Ext.comp_assoc
    (Ext.mk₀ (supportedWholeCoefficientOneAugmentation217 K kappa))
    ((Ext.mk₀ K.hom).comp (alpha.comp (Ext.mk₀ b) (add_zero 1)) (zero_add 1))
    delta (zero_add 1) rfl (show 0 + 1 + 1 = 2 by rfl)
  rw [← hAssoc, Ext.mk₀_comp_mk₀_assoc,
    supportedWholeCoefficientOneAugmentation_comp217]

end PfaffianDescent
