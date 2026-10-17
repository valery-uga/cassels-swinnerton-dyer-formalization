import PfaffianDescent.CubicPointTraceFieldBaseChangeStalkPullback
import PfaffianDescent.CubicPointTraceFieldBaseChangeFlatScalars
import PfaffianDescent.SchemeModuleStalkMono
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Exactness of actual flat scheme-module pullback

This proves exactness for the actual scheme-module pullback functor, using
its actual local-ring stalk comparison. No cohomological comparison is assumed.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual pullback along a flat scheme morphism sends a monomorphism to a
monomorphism. -/
theorem cubicPointTraceFieldBaseChangeFlatPullback_map_mono
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {M N : Y.Modules} (φ : M ⟶ N) [Mono φ] :
    Mono ((Scheme.Modules.pullback f).map φ) := by
  apply schemeModule_mono_of_stalk_mono
  intro x
  letI := cubicPointTraceFieldBaseChangeFlatScalarsPreservesMonomorphisms
    (f.stalkMap x).hom (Flat.stalkMap f x)
  letI : (Scheme.Modules.pullback f ⋙
      schemeModuleStalkModuleFunctor X x).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso
      (cubicPointTraceFieldBaseChangeStalkPullbackNatIso f x).symm
  have hm : Mono ((schemeModuleStalkModuleFunctor X x).map
      ((Scheme.Modules.pullback f).map φ)) :=
    Functor.map_mono (Scheme.Modules.pullback f ⋙ schemeModuleStalkModuleFunctor X x) φ
  rw [AddCommGrpCat.mono_iff_injective]
  exact (ModuleCat.mono_iff_injective _).mp hm

noncomputable instance cubicPointTraceFieldBaseChangeFlatPullbackPreservesMonomorphisms
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (Scheme.Modules.pullback f).PreservesMonomorphisms where
  preserves {M N} φ hφ :=
    @cubicPointTraceFieldBaseChangeFlatPullback_map_mono X Y f _ M N φ hφ

/-- Actual flat pullback preserves homology. -/
theorem cubicPointTraceFieldBaseChangeFlatPullbackPreservesHomology
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    (Scheme.Modules.pullback f).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- The actual flat pullback is an exact functor, with its already available
finite-colimit preservation and the finite-limit preservation proved here. -/
noncomputable instance cubicPointTraceFieldBaseChangeFlatPullbackPreservesFiniteLimits
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    PreservesFiniteLimits (Scheme.Modules.pullback f) := by
  letI := cubicPointTraceFieldBaseChangeFlatPullbackPreservesHomology f
  exact Functor.preservesFiniteLimits_of_preservesHomology _

end PfaffianDescent
