import PfaffianDescent.CubicPointTraceFieldBaseChangePointSummand
import PfaffianDescent.CubicPointTraceFieldBaseChangeOpenSupportStalk
import PfaffianDescent.PointCartierNativeStalkPushforwardComparison

/-! The actual separable diagonal summand is the whole support on its
native rational-point stalk. No chosen stalk comparison is a premise. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual native closed-pushforward comparison transports invertibility
of a map on its source stalk; it preserves the original scalar restriction. -/
theorem nativeClosedPushforward_stalk_map_isIso222
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X)
    {M N : X.Modules} (a : M ⟶ N)
    [IsIso ((schemeModuleStalkModuleFunctor X x).map a)] :
    IsIso ((schemeModuleStalkModuleFunctor Y (f x)).map
      ((Scheme.Modules.pushforward f).map a)) := by
  let e := pointCartierNativeStalkPushforwardNatIso f f.isClosedEmbedding.isInducing x
  have h : IsIso ((schemeModuleStalkModuleFunctor X x ⋙
      ModuleCat.restrictScalars (f.stalkMap x).hom).map a) := by
    dsimp only [Functor.comp_map]
    infer_instance
  exact (NatIso.isIso_map_iff e a).mpr h

section
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (i : Spec (.of L) ⟶ X)
  (hi : i ≫ p = Spec.map (CommRingCat.ofHom (algebraMap K L)))
  [IsClosedImmersion i]

/-- At the actual rational diagonal point, restriction from the whole
tensor support is an isomorphism of the original native stalk modules. -/
theorem cubicPointTraceFieldBaseChangePointSummandRestriction_stalk_isIso222 :
    let d := cubicPointTraceFieldBaseChangeTensorDiagonal K L
    let j := cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi
    let x := d (default : Spec (.of L))
    IsIso ((schemeModuleStalkModuleFunctor
      (schemeBaseChangeToField (L := L) X p) (j x)).map
        (cubicPointTraceFieldBaseChangePointSummandRestriction K L p i hi)) := by
  dsimp only
  let d := cubicPointTraceFieldBaseChangeTensorDiagonal K L
  let j := cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi
  let x := d (default : Spec (.of L))
  let q := IdealSheafDataModule.closedImmersionUnitToPushforwardUnit d
  letI : Algebra.FormallyUnramified K L := Algebra.FormallyUnramified.of_isSeparable K L
  letI : IsOpenImmersion d := by
    dsimp only [d, cubicPointTraceFieldBaseChangeTensorDiagonal]
    infer_instance
  letI : IsIso ((schemeModuleStalkModuleFunctor (Spec (.of (L ⊗[K] L))) x).map q) :=
    cubicPointTraceFieldBaseChangeOpenSupportUnitStalk_isIso d (default : Spec (.of L))
  letI : IsIso ((schemeModuleStalkModuleFunctor
      (schemeBaseChangeToField (L := L) X p) (j x)).map
      ((Scheme.Modules.pushforward j).map q)) :=
    nativeClosedPushforward_stalk_map_isIso222 j x q
  change IsIso ((schemeModuleStalkModuleFunctor
      (schemeBaseChangeToField (L := L) X p) (j x)).map
      ((Scheme.Modules.pushforward j).map q ≫
        (cubicPointTraceFieldBaseChangeDiagonalAmbientPushforwardIso K L p i hi).hom))
  rw [Functor.map_comp]
  infer_instance

/-- The canonical separability section is invertible on that SAME native
stalk, derived from the genuine section/restriction identity. -/
theorem cubicPointTraceFieldBaseChangePointSummandSection_stalk_isIso222 :
    let d := cubicPointTraceFieldBaseChangeTensorDiagonal K L
    let j := cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi
    let x := d (default : Spec (.of L))
    IsIso ((schemeModuleStalkModuleFunctor
      (schemeBaseChangeToField (L := L) X p) (j x)).map
        (cubicPointTraceFieldBaseChangePointSummandSection K L p i hi)) := by
  dsimp only
  let H := schemeModuleStalkModuleFunctor (schemeBaseChangeToField (L := L) X p)
    ((cubicPointTraceFieldBaseChangeTensorPointToAmbient K L p i hi)
      ((cubicPointTraceFieldBaseChangeTensorDiagonal K L) (default : Spec (.of L))))
  let q := cubicPointTraceFieldBaseChangePointSummandRestriction K L p i hi
  let s := cubicPointTraceFieldBaseChangePointSummandSection K L p i hi
  letI : IsIso (H.map q) :=
    cubicPointTraceFieldBaseChangePointSummandRestriction_stalk_isIso222 K L p i hi
  apply isIso_of_comp_hom_eq_id (H.map q)
  rw [← H.map_comp, cubicPointTraceFieldBaseChangePointSummandSection_restriction,
    H.map_id]

end
end PfaffianDescent
