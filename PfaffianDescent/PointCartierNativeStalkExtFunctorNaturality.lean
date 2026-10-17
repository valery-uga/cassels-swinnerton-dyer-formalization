import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-! # Exact-functor Ext maps respect an actual natural transformation

This is proved by injective dimension shifting in the source category.
It supplies the missing naturality statement for the native stalk comparison.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe u v w u' v' w' u'' v'' w''

attribute [local instance] Ext.subsingleton_of_injective in
theorem pointCartierNativeStalkExtFunctorNaturality
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [hExtC : HasExt.{w} C] [hExtD : HasExt.{w'} D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ⟶ G) {X Y : C} {n : ℕ} (α : Ext.{w} X Y n) :
    (α.mapExactFunctor F).comp (Ext.mk₀ (e.app Y)) (add_zero n) =
      (Ext.mk₀ (e.app X)).comp (α.mapExactFunctor G) (zero_add n) := by
  induction n generalizing Y with
  | zero =>
      obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective X Y).2 α
      rw [Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀,
        Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
      exact congrArg Ext.mk₀ (e.naturality a)
  | succ n hn =>
      let I : InjectivePresentation Y := Classical.arbitrary _
      let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
      haveI : Injective S.X₂ := I.injective
      obtain ⟨γ, hγ⟩ := Ext.covariant_sequence_exact₁ X hS α (by subsingleton) rfl
      rw [← hγ, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp,
        Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_extClass]
      have hc := ShortComplex.ShortExact.extClass_naturality
        (hS.map_of_exact F) (hS.map_of_exact G) (S.mapNatTrans e)
      change (hS.map_of_exact F).extClass.comp (Ext.mk₀ (e.app Y)) (add_zero 1) =
        (Ext.mk₀ (e.app S.X₃)).comp (hS.map_of_exact G).extClass (zero_add 1) at hc
      rw [Ext.comp_assoc_of_third_deg_zero, hc,
        ← Ext.comp_assoc_of_second_deg_zero, hn γ]
      exact Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)

attribute [local instance] Ext.subsingleton_of_injective in
theorem pointCartierNativeStalkExtFunctorComposition
    {C : Type u} [Category.{v} C] [Abelian C] [EnoughInjectives C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    {E : Type u''} [Category.{v''} E] [Abelian E]
    [hExtC : HasExt.{w} C] [hExtD : HasExt.{w'} D] [hExtE : HasExt.{w''} E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {X Y : C} {n : ℕ} (α : Ext.{w} X Y n) :
    (α.mapExactFunctor F).mapExactFunctor G = α.mapExactFunctor (F ⋙ G) := by
  induction n generalizing Y with
  | zero =>
      obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective X Y).2 α
      simp only [Ext.mapExactFunctor_mk₀, Functor.comp_map]
  | succ n hn =>
      let I : InjectivePresentation Y := Classical.arbitrary _
      let S := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
      haveI : Injective S.X₂ := I.injective
      obtain ⟨γ, hγ⟩ := Ext.covariant_sequence_exact₁ X hS α (by subsingleton) rfl
      rw [← hγ, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp,
        Ext.mapExactFunctor_comp, hn γ,
        Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_extClass,
        Ext.mapExactFunctor_extClass]


end PfaffianDescent
