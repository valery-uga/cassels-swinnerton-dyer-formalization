import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Trace.Basic

/-!
# Trace-selected one-dimensional quotients

The abstract linear-algebra step in Proposition 4.3: a six-dimensional
`K`-space mapping to a two-dimensional `L`-space admits a one-dimensional
`L`-quotient whose composite has a kernel of dimension at least three.
-/

namespace PfaffianDescent
namespace QuarticNet

open Module LinearMap

section

variable (K L E : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [AddCommGroup E] [Module L E] [Module K E] [IsScalarTower K L E]
  [FiniteDimensional L E] [FiniteDimensional K E]

/-- Composition with the trace map, viewed as a map of `K`-duals. -/
noncomputable def traceQuotientDualMap : (E →ₗ[L] L) →ₗ[K] (E →ₗ[K] K) where
  toFun f := (Algebra.trace K L).comp (f.restrictScalars K)
  map_add' f g := by ext x; simp
  map_smul' r f := by ext x; simp

omit [FiniteDimensional L E] [FiniteDimensional K E] in
theorem traceQuotientDualMap_injective : Function.Injective (traceQuotientDualMap K L E) := by
  intro f g h
  apply sub_eq_zero.mp
  by_contra hn
  have hs : Function.Surjective (f - g) :=
    surjective_of_nonzero_of_finrank_eq_one (finrank_self L) hn
  obtain ⟨y, hy⟩ := Algebra.trace_surjective K L 1
  obtain ⟨x, hx⟩ := hs y
  have hval : Algebra.trace K L (f x) = Algebra.trace K L (g x) :=
    congrArg (fun q : E →ₗ[K] K => q x) h
  have hz : Algebra.trace K L ((f - g) x) = 0 := by
    change Algebra.trace K L (f x - g x) = 0
    rw [map_sub, hval, sub_self]
  rw [hx, hy] at hz
  exact one_ne_zero hz

theorem traceQuotientDualMap_bijective : Function.Bijective (traceQuotientDualMap K L E) := by
  have hd : Module.finrank K (E →ₗ[L] L) = Module.finrank K (E →ₗ[K] K) := by
    rw [Module.finrank_linearMap, Module.finrank_linearMap, finrank_self, mul_one]
    rw [mul_comm, Module.finrank_mul_finrank K L E]
  exact ⟨traceQuotientDualMap_injective K L E,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp
      (traceQuotientDualMap_injective K L E)⟩

end

section

variable {K L E V : Type*} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [AddCommGroup E] [Module L E] [Module K E] [IsScalarTower K L E]
  [FiniteDimensional L E] [FiniteDimensional K E]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The dimension count supplies a nonzero `K`-functional annihilating a
map from a six-dimensional space into an eight-dimensional one. -/
theorem annihilating_functional_exists (φ : V →ₗ[K] E)
    (hE : Module.finrank K E = 8) (hV : Module.finrank K V = 6) :
    ∃ ell : E →ₗ[K] K, ell ≠ 0 ∧ ell.comp φ = 0 := by
  have hd : Module.finrank K (V →ₗ[K] K) < Module.finrank K (E →ₗ[K] K) := by
    simp [Module.finrank_linearMap, hE, hV]
  have hker : LinearMap.ker φ.dualMap ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hd
  obtain ⟨ell, hell, hann⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨ell, hann, hell⟩

/-- The trace construction produces a surjective `L`-linear functional whose
composite with `φ` has a kernel of `K`-dimension at least three. -/
theorem quotient_with_large_kernel (φ : V →ₗ[K] E)
    (hL : Module.finrank K L = 4) (hE : Module.finrank L E = 2)
    (hV : Module.finrank K V = 6) :
    ∃ q : E →ₗ[L] L, Function.Surjective q ∧
      (Algebra.trace K L).comp ((q.restrictScalars K).comp φ) = 0 ∧
      3 ≤ Module.finrank K (LinearMap.ker ((q.restrictScalars K).comp φ)) := by
  have hEK : Module.finrank K E = 8 := by
    rw [← Module.finrank_mul_finrank K L E, hL, hE]
  obtain ⟨ell, hell, hann⟩ := annihilating_functional_exists φ hEK hV
  obtain ⟨q, hq⟩ := (traceQuotientDualMap_bijective K L E).surjective ell
  have hqne : q ≠ 0 := by
    intro hz
    apply hell
    rw [hz, map_zero] at hq
    exact hq.symm
  have hqsurj : Function.Surjective q :=
    surjective_of_nonzero_of_finrank_eq_one (finrank_self L) hqne
  let g : V →ₗ[K] L := (q.restrictScalars K).comp φ
  have htrace : (Algebra.trace K L).comp g = 0 := by
    change ((traceQuotientDualMap K L E) q).comp φ = 0
    rw [hq, hann]
  have hproper : LinearMap.range g ≠ ⊤ := by
    intro htop
    have hgs : Function.Surjective g := LinearMap.range_eq_top.mp htop
    apply Algebra.trace_ne_zero K L
    ext y
    obtain ⟨v, rfl⟩ := hgs y
    exact congrArg (fun m : V →ₗ[K] K => m v) htrace
  have hlt : Module.finrank K (LinearMap.range g) < 4 := by
    simpa [hL] using Submodule.finrank_lt hproper
  have hr := g.finrank_range_add_finrank_ker
  rw [hV] at hr
  refine ⟨q, hqsurj, htrace, ?_⟩
  change 3 ≤ Module.finrank K (LinearMap.ker g)
  omega

end
end QuarticNet
end PfaffianDescent
