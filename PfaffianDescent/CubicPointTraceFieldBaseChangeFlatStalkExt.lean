import PfaffianDescent.CubicPointTraceFieldBaseChangeFlatExt
import PfaffianDescent.CubicPointTraceFieldBaseChangeLocalExt
import PfaffianDescent.PointCartierNativeStalkExtFunctorNaturality

/-! # Actual flat native Ext pullback at the actual local-ring map -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Native pullback followed by the actual stalk map is actual local flat
tensor pullback, under the constructed stalk comparison. -/
theorem cubicPointTraceFieldBaseChangeFlatPullbackStalkExt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X)
    [EnoughInjectives Y.Modules]
    [HasExt.{u} Y.Modules] [HasExt.{u} X.Modules]
    [HasExt.{u + 1} (ModuleCat.{u} (Y.presheaf.stalk (f x)))]
    [HasExt.{u + 1} (ModuleCat.{u} (X.presheaf.stalk x))]
    {M N : Y.Modules} (n : ℕ) (z : Ext.{u} M N n) :
    ((cubicPointTraceFieldBaseChangeFlatPullbackExtMap f M N n z).mapExactFunctor
      (schemeModuleStalkModuleFunctor X x)).comp
      (Ext.mk₀.{u + 1} (C := ModuleCat.{u} (X.presheaf.stalk x))
        ((cubicPointTraceFieldBaseChangeStalkPullbackNatIso f x).app N).hom)
      (add_zero n) =
    (Ext.mk₀.{u + 1} (C := ModuleCat.{u} (X.presheaf.stalk x))
      ((cubicPointTraceFieldBaseChangeStalkPullbackNatIso f x).app M).hom).comp
      (cubicPointTraceFieldBaseChangeLocalExtMap (f.stalkMap x).hom (Flat.stalkMap f x)
        ((schemeModuleStalkModuleFunctor Y (f x)).obj M)
        ((schemeModuleStalkModuleFunctor Y (f x)).obj N) n
        (z.mapExactFunctor (schemeModuleStalkModuleFunctor Y (f x)))) (zero_add n) := by
  letI := cubicPointTraceFieldBaseChangeLocalScalarsPreservesFiniteLimits
    (f.stalkMap x).hom (Flat.stalkMap f x)
  change ((z.mapExactFunctor (Scheme.Modules.pullback f)).mapExactFunctor
    (schemeModuleStalkModuleFunctor X x)).comp _ (add_zero n) =
    (Ext.mk₀.{u + 1} (C := ModuleCat.{u} (X.presheaf.stalk x)) _).comp
      ((z.mapExactFunctor (schemeModuleStalkModuleFunctor Y (f x))).mapExactFunctor
        (ModuleCat.extendScalars (f.stalkMap x).hom)) (zero_add n)
  rw [pointCartierNativeStalkExtFunctorComposition,
    pointCartierNativeStalkExtFunctorComposition]
  exact pointCartierNativeStalkExtFunctorNaturality _ _
    (cubicPointTraceFieldBaseChangeStalkPullbackNatIso f x).hom z

end PfaffianDescent
