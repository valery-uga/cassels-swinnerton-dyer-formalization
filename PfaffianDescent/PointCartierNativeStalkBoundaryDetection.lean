import PfaffianDescent.PointCartierNativeStalkPushforwardExt

/-! # Detection of the actual Cartier boundary by the actual stalk functor -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u v w u' v' w'

theorem pointCartierNativeStalkExactBoundary_nonzero
    {C : Type u} [Category.{v} C] [Abelian C]
    {D : Type u'} [Category.{v'} D] [Abelian D]
    [hExtC : HasExt.{w} C] [hExtD : HasExt.{w'} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (S : ShortComplex C) (hS : S.ShortExact) (M : C) (z : Ext.{w} M S.X₃ 2)
    [Subsingleton (Ext.{w'} (F.obj M) (F.obj S.X₂) 2)]
    (hz : z.mapExactFunctor F ≠ 0) : z.comp hS.extClass rfl ≠ 0 := by
  intro hzero
  have hmap := congrArg (fun a ↦ a.mapExactFunctor F) hzero
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    Ext.mapExactFunctor_zero] at hmap
  letI : Subsingleton (Ext.{w'} (F.obj M) (S.map F).X₂ 2) := by
    change Subsingleton (Ext.{w'} (F.obj M) (F.obj S.X₂) 2)
    infer_instance
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₃ _ (hS.map_of_exact F)
    (z.mapExactFunctor F) rfl hmap
  have hb0 : b = 0 := Subsingleton.elim _ _
  rw [hb0, Ext.zero_comp] at hb
  exact hz hb.symm

theorem pointCartierNativeStalkPushforwardExt_nonzero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X)
    [EnoughInjectives X.Modules]
    [hExtX : HasExt.{u} X.Modules] [hExtY : HasExt.{u} Y.Modules]
    [hExtLocalX : HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    [hExtLocalY : HasExt.{u + 1} (ModuleCat (Y.presheaf.stalk (f x)))]
    {M N : X.Modules} {n : ℕ} (z : Ext.{u} M N n)
    (hz : (z.mapExactFunctor (schemeModuleStalkModuleFunctor X x)).mapExactFunctor
      (ModuleCat.restrictScalars (f.stalkMap x).hom) ≠ 0) :
    (z.mapExactFunctor (Scheme.Modules.pushforward f)).mapExactFunctor
      (schemeModuleStalkModuleFunctor Y (f x)) ≠ 0 := by
  intro hzero
  have hnat := pointCartierNativeStalkPushforwardExt f x z
  rw [hzero, Ext.zero_comp] at hnat
  let eM := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x M
  have heq := congrArg (fun b ↦ (Ext.mk₀ eM.inv).comp b (zero_add n)) hnat
  apply hz
  simpa only [eM, Ext.comp_zero, Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id,
    Ext.mk₀_id_comp] using heq.symm

end PfaffianDescent
