import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat

/-! # Exact scalar extension along an actual flat ring homomorphism -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual extension of scalars along a flat ring map preserves monomorphisms. -/
theorem cubicPointTraceFieldBaseChangeFlatScalars_map_mono
    {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) (hg : g.Flat)
    {M N : ModuleCat.{u} R} (φ : M ⟶ N) [Mono φ] :
    Mono ((ModuleCat.extendScalars g).map φ) := by
  letI := g.toAlgebra
  letI : Module.Flat R S := hg
  rw [ModuleCat.mono_iff_injective]
  have hφ : Function.Injective φ.hom := (ModuleCat.mono_iff_injective φ).mp inferInstance
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := S) φ.hom hφ
  change Function.Injective (φ.hom.baseChange S)
  simpa only [LinearMap.baseChange_eq_ltensor] using h

/-- The monomorphism preservation is attached to the actual scalar-extension
functor, rather than to an isomorphic surrogate. -/
theorem cubicPointTraceFieldBaseChangeFlatScalarsPreservesMonomorphisms
    {R S : Type u} [CommRing R] [CommRing S] (g : R →+* S) (hg : g.Flat) :
    (ModuleCat.extendScalars.{u, u, u} g).PreservesMonomorphisms where
  preserves {M N} φ hφ :=
    @cubicPointTraceFieldBaseChangeFlatScalars_map_mono R S _ _ g hg M N φ hφ

end PfaffianDescent
