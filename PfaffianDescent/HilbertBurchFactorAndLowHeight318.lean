import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
Two steps in determinantal ideal identification: descend a functional
through a surjective presentation when it annihilates the kernel, and
prove a scalar is a unit by excluding low-height prime membership.
-/

namespace AllCharacteristics.HilbertSurfaceDraft

/-- A row annihilating all relations of a surjective presentation descends
to a functional on the presented module. -/
theorem exists_linearMap_factor_of_ker_le
    {R F N P : Type*} [Ring R]
    [AddCommGroup F] [Module R F]
    [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P]
    (f : F →ₗ[R] N) (hf : Function.Surjective f)
    (ψ : F →ₗ[R] P) (hker : LinearMap.ker f ≤ LinearMap.ker ψ) :
    ∃ φ : N →ₗ[R] P, φ.comp f = ψ := by
  let e := f.quotKerEquivOfSurjective hf
  let φ : N →ₗ[R] P :=
    ((LinearMap.ker f).liftQ ψ hker).comp e.symm.toLinearMap
  refine ⟨φ, ?_⟩
  ext v
  change (LinearMap.ker f).liftQ ψ hker (e.symm (f v)) = ψ v
  have he : e (Submodule.Quotient.mk v) = f v :=
    f.quotKerEquivOfSurjective_apply_mk hf v
  rw [← he, e.symm_apply_apply]
  rfl

/-- The principal ideal theorem reduces proving a scalar is a unit to
excluding membership in every prime of height at most one. -/
theorem isUnit_of_not_mem_prime_height_le_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] (a : R)
    (h : ∀ p : Ideal R, p.IsPrime → p.height ≤ 1 → a ∉ p) :
    IsUnit a := by
  by_contra ha
  obtain ⟨p, hp⟩ :=
    (Ideal.span ({a} : Set R)).nonempty_minimalPrimes (Ideal.span_singleton_ne_top ha)
  exact h p hp.1.1
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span ({a} : Set R)) p hp)
    (hp.1.2 (Ideal.mem_span_singleton_self a))

end AllCharacteristics.HilbertSurfaceDraft
