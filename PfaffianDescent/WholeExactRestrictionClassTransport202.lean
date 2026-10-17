import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-! Whole exact sequence naturality transports an actual extension and
its projection under an exact functor Iso. No class identity is assumed. -/
noncomputable section
namespace PfaffianDescent
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u u' v v' w

/-- The augmentation and endpoint coordinate are transported together.
Both sides are classes of the ORIGINAL mapped whole short exact sequence. -/
theorem wholeExactNaturalIso_normalizedClass202
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{w} D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (S : ShortComplex C) (hS : S.ShortExact)
    (M N : D) (kappa : M ⟶ G.obj S.X₃) (b : G.obj S.X₁ ⟶ N) :
    (Ext.mk₀ (kappa ≫ (e.app S.X₃).inv)).comp
        ((hS.map_of_exact F).extClass.comp
          (Ext.mk₀ ((e.app S.X₁).hom ≫ b)) (add_zero 1)) (zero_add 1) =
      (Ext.mk₀ kappa).comp
        ((hS.map_of_exact G).extClass.comp (Ext.mk₀ b) (add_zero 1)) (zero_add 1) := by
  let zF : Ext.{w} (F.obj S.X₃) (F.obj S.X₁) 1 := (hS.map_of_exact F).extClass
  let zG : Ext.{w} (G.obj S.X₃) (G.obj S.X₁) 1 := (hS.map_of_exact G).extClass
  have hn : zF.comp (Ext.mk₀ (e.app S.X₁).hom) (add_zero 1) =
      (Ext.mk₀ (e.app S.X₃).hom).comp zG (zero_add 1) :=
    (hS.map_of_exact F).extClass_naturality (hS.map_of_exact G) (S.mapNatIso e).hom
  change (Ext.mk₀ (kappa ≫ (e.app S.X₃).inv)).comp
      (zF.comp (Ext.mk₀ ((e.app S.X₁).hom ≫ b)) (add_zero 1)) (zero_add 1) =
    (Ext.mk₀ kappa).comp (zG.comp (Ext.mk₀ b) (add_zero 1)) (zero_add 1)
  have hb : zF.comp (Ext.mk₀ ((e.app S.X₁).hom ≫ b)) (add_zero 1) =
      (Ext.mk₀ (e.app S.X₃).hom).comp
        (zG.comp (Ext.mk₀ b) (add_zero 1)) (zero_add 1) := by
    rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
      hn, Ext.comp_assoc_of_third_deg_zero]
  rw [hb, Ext.mk₀_comp_mk₀_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The actual sequence projection square is retained under the SAME
inverse functor comparison as the preceding class identity. -/
lemma wholeExactNaturalIso_projection202
    {C : Type u} [Category.{v} C]
    {D : Type u'} [Category.{v'} D]
    (F G : C ⥤ D) (e : F ≅ G) (X Y : C) (g : X ⟶ Y)
    (M : D) (b : M ⟶ G.obj X) :
    (b ≫ (e.app X).inv) ≫ F.map g = (b ≫ G.map g) ≫ (e.app Y).inv := by
  have hn : (e.app X).inv ≫ F.map g = G.map g ≫ (e.app Y).inv :=
    (e.inv.naturality g).symm
  exact (Category.assoc b (e.app X).inv (F.map g)).trans
    ((congrArg (fun h => b ≫ h) hn).trans
      (Category.assoc b (G.map g) (e.app Y).inv).symm)

end PfaffianDescent
