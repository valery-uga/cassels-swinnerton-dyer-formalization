import PfaffianDescent.PointCartierNativeStalkPushforwardComparison

/-! Assemble the EXISTING native pushforward-stalk NatIso on a whole
original short complex; no new stalk-map or naturality proof is duplicated. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Both original arrows and the actual native pushforward-stalk maps
are preserved by this whole sequence comparison. -/
def nativePushforwardWholeStalkSequenceIso206
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X)
    (S : ShortComplex X.Modules) :
    (S.map (Scheme.Modules.pushforward f)).map
        (schemeModuleStalkModuleFunctor Y (f x)) ≅
      (S.map (schemeModuleStalkModuleFunctor X x)).map
        (ModuleCat.restrictScalars (f.stalkMap x).hom) :=
  S.mapNatIso (pointCartierNativeStalkPushforwardNatIso f
    f.isClosedEmbedding.isInducing x)

end PfaffianDescent
