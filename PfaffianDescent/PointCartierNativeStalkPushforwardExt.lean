import PfaffianDescent.PointCartierNativeStalkPushforwardComparison
import PfaffianDescent.PointCartierNativeStalkExtFunctorNaturality

/-! # Actual Ext compatibility of closed-immersion pushforward and stalk

Both routes apply the native exact functors. Their endpoint identifications
are the proved module-linear stalk-pushforward isomorphism.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe u

theorem pointCartierNativeStalkPushforwardExt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X)
    [EnoughInjectives X.Modules]
    [hExtX : HasExt.{u} X.Modules] [hExtY : HasExt.{u} Y.Modules]
    [hExtLocalX : HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    [hExtLocalY : HasExt.{u + 1} (ModuleCat (Y.presheaf.stalk (f x)))]
    {M N : X.Modules} {n : ℕ} (α : Ext.{u} M N n) :
    ((α.mapExactFunctor (Scheme.Modules.pushforward f)).mapExactFunctor
        (schemeModuleStalkModuleFunctor Y (f x))).comp
      (Ext.mk₀ (pointCartierNativeStalkPushforwardIso f
        f.isClosedEmbedding.isInducing x N).hom) (add_zero n) =
    (Ext.mk₀ (pointCartierNativeStalkPushforwardIso f
      f.isClosedEmbedding.isInducing x M).hom).comp
      ((α.mapExactFunctor (schemeModuleStalkModuleFunctor X x)).mapExactFunctor
        (ModuleCat.restrictScalars (f.stalkMap x).hom)) (zero_add n) := by
  rw [pointCartierNativeStalkExtFunctorComposition,
    pointCartierNativeStalkExtFunctorComposition]
  exact pointCartierNativeStalkExtFunctorNaturality _ _
    (pointCartierNativeStalkPushforwardNatIso f f.isClosedEmbedding.isInducing x).hom α

end PfaffianDescent
