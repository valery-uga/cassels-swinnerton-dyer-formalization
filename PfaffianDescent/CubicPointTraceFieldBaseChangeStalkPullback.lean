import PfaffianDescent.CubicPointTraceFieldBaseChangeSkyscraper
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Stalks of actual scheme-module pullback

The comparison is derived from the actual pullback and stalk adjunctions.
The ring map is the actual morphism on local rings.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Taking a stalk after actual scheme-module pullback is actual extension of
scalars of the original stalk by the scheme's local-ring map. -/
def cubicPointTraceFieldBaseChangeStalkPullbackNatIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    Scheme.Modules.pullback f ⋙ schemeModuleStalkModuleFunctor X x ≅
      schemeModuleStalkModuleFunctor Y (f x) ⋙
        ModuleCat.extendScalars (f.stalkMap x).hom :=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (schemeModuleStalkSkyscraperAdjunction X x)).ofNatIsoRight
        (cubicPointTraceFieldBaseChangeSkyscraperPushforwardNatIso f x)).leftAdjointUniq
    ((schemeModuleStalkSkyscraperAdjunction Y (f x)).comp
      (ModuleCat.extendRestrictScalarsAdj (f.stalkMap x).hom))

end PfaffianDescent
