import PfaffianDescent.AffineSourceChartBaseChange

/-!
# Closed-immersion ideal base change from relative exactness

The quotient pushforward and its kernel commute with arbitrary base
change. Thus, for an ideal whose inclusion remains monic after pullback,
the canonical ideal-module base-change map is an isomorphism, even when
the base-change morphism is not flat.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/-- The canonical closed-immersion ideal-module comparison is an
isomorphism as soon as the pulled-back ideal inclusion is monic. -/
theorem isIso_closedImmersionIdealBaseChangeHom_of_pullback_mono
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i]
    [Mono ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i))] :
    IsIso (closedImmersionIdealBaseChangeHom f i) := by
  haveI : IsIso (closedImmersionIdealPullbackKernelComparison f i) :=
    isIso_closedImmersionIdealPullbackKernelComparison_of_mono f i
  haveI : IsIso (closedImmersionPushforwardBaseChangeKernelMap f i) :=
    isIso_closedImmersionPushforwardBaseChangeKernelMap_general f i
  let a := closedImmersionIdealPullbackKernelComparison f i
  let k := closedImmersionPushforwardBaseChangeKernelMap f i
  let m := IdealSheafDataModule.closedImmersionModuleToKernelIso (pullback.fst f i)
  change IsIso (a ≫ k ≫ m.inv)
  have hak : IsIso (a ≫ k) :=
    IsIso.comp_isIso' (f := a) (h := k)
      (by infer_instance) (by infer_instance)
  exact IsIso.comp_isIso' (f := a ≫ k) (h := m.inv) hak m.isIso_inv

/-- It suffices to check preservation of the ideal inclusion on an open
cover of the source. The resulting isomorphism is the canonical global
ideal base-change map, so no separate overlap choices are required. -/
theorem isIso_closedImmersionIdealBaseChangeHom_of_openCover_comp_mono
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (i : Z ⟶ Y)
    [IsClosedImmersion i] (𝒰 : X.OpenCover)
    (h : ∀ a : 𝒰.I₀, Mono
      ((Scheme.Modules.pullback ((𝒰.f a) ≫ f)).map
        (IdealSheafDataModule.closedImmersionModuleToUnit i))) :
    IsIso (closedImmersionIdealBaseChangeHom f i) := by
  haveI : Mono ((Scheme.Modules.pullback f).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) := by
    apply schemeModule_mono_of_openCover_restrict_mono 𝒰 _
    intro a
    exact restrict_pullback_map_mono_of_comp (𝒰.f a) f _ (h a)
  exact isIso_closedImmersionIdealBaseChangeHom_of_pullback_mono f i

end PfaffianDescent
