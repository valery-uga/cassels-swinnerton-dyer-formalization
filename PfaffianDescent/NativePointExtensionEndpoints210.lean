import PfaffianDescent.PointCartierNativeStalkPushforwardExt

/-! Compose the EXISTING native pushforward-stalk Ext comparison with
ordinary original endpoint maps. No naturality law is supplied as a premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe u
set_option backward.isDefEq.respectTransparency false

theorem nativeClosedPushforwardExt_originalEndpoints210
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X)
    [EnoughInjectives X.Modules]
    [HasExt.{u} X.Modules] [HasExt.{u} Y.Modules]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    [HasExt.{u + 1} (ModuleCat (Y.presheaf.stalk (f x)))]
    {M N : X.Modules} (alpha : Ext.{u} M N 1)
    {T P : ModuleCat (Y.presheaf.stalk (f x))}
    (b : T ⟶ (schemeModuleStalkModuleFunctor Y (f x)).obj
      ((Scheme.Modules.pushforward f).obj M))
    (t : (schemeModuleStalkModuleFunctor Y (f x)).obj
      ((Scheme.Modules.pushforward f).obj N) ⟶ P) :
    (Ext.mk₀ b).comp
      (((alpha.mapExactFunctor (Scheme.Modules.pushforward f)).mapExactFunctor
          (schemeModuleStalkModuleFunctor Y (f x))).comp (Ext.mk₀ t) (add_zero 1))
      (zero_add 1) =
      (Ext.mk₀ (b ≫ (pointCartierNativeStalkPushforwardIso f
        f.isClosedEmbedding.isInducing x M).hom)).comp
        (((alpha.mapExactFunctor (schemeModuleStalkModuleFunctor X x)).mapExactFunctor
          (ModuleCat.restrictScalars (f.stalkMap x).hom)).comp
            (Ext.mk₀ ((pointCartierNativeStalkPushforwardIso f
              f.isClosedEmbedding.isInducing x N).inv ≫ t)) (add_zero 1))
        (zero_add 1) := by
  let etaM := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x M
  let etaN := pointCartierNativeStalkPushforwardIso f f.isClosedEmbedding.isInducing x N
  let A := (alpha.mapExactFunctor (Scheme.Modules.pushforward f)).mapExactFunctor
    (schemeModuleStalkModuleFunctor Y (f x))
  let B := (alpha.mapExactFunctor (schemeModuleStalkModuleFunctor X x)).mapExactFunctor
    (ModuleCat.restrictScalars (f.stalkMap x).hom)
  have hn : A.comp (Ext.mk₀ etaN.hom) (add_zero 1) =
      (Ext.mk₀ etaM.hom).comp B (zero_add 1) :=
    pointCartierNativeStalkPushforwardExt f x alpha
  have hpost : A.comp (Ext.mk₀ t) (add_zero 1) =
      (Ext.mk₀ etaM.hom).comp
        (B.comp (Ext.mk₀ (etaN.inv ≫ t)) (add_zero 1)) (zero_add 1) := by
    calc
      _ = (A.comp (Ext.mk₀ etaN.hom) (add_zero 1)).comp
          (Ext.mk₀ (etaN.inv ≫ t)) (add_zero 1) := by
        rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
          ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
      _ = _ := by rw [hn, Ext.comp_assoc_of_third_deg_zero]
  change (Ext.mk₀ b).comp (A.comp (Ext.mk₀ t) (add_zero 1)) (zero_add 1) = _
  rw [hpost, Ext.mk₀_comp_mk₀_assoc]

end PfaffianDescent
