import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Completeness of finite free modules

Adic completeness is invariant under linear equivalence and holds for finite
products of a complete ring. A finite basis therefore proves completeness of
the corresponding module. This will be applied to monic root algebras when
lifting residue-field extensions.
-/

namespace AllCharacteristics
universe u v w

/-- Adic completeness transports along a linear equivalence. -/
theorem isAdicComplete_of_linearEquiv
    {R : Type u} [CommRing R] (I : Ideal R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]
    [IsAdicComplete I M] (e : M ≃ₗ[R] N) : IsAdicComplete I N := by
  apply (AdicCompletion.of_bijective_iff (I := I) (M := N)).mp
  have h : Function.Bijective (fun x : N ↦
      AdicCompletion.congr I e (AdicCompletion.of I M (e.symm x))) :=
    (AdicCompletion.congr I e).bijective.comp
      ((AdicCompletion.of_bijective I M).comp e.symm.bijective)
  have he : (fun x : N ↦ AdicCompletion.congr I e (AdicCompletion.of I M (e.symm x))) =
      AdicCompletion.of I N := by
    funext x
    change AdicCompletion.map I e.toLinearMap (AdicCompletion.of I M (e.symm x)) = _
    rw [AdicCompletion.map_of]
    exact congrArg (AdicCompletion.of I N) (e.apply_symm_apply x)
  exact he ▸ h

/-- A finite product of copies of an adically complete ring is complete as
a module for the same ideal. -/
theorem isAdicComplete_finite_pi
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (ι : Type v) [Fintype ι] : IsAdicComplete I (ι → R) := by
  classical
  let e := AdicCompletion.piEquivOfFintype I (fun _ : ι ↦ R)
  apply (AdicCompletion.of_bijective_iff (I := I) (M := ι → R)).mp
  constructor
  · intro f g h
    funext i
    apply AdicCompletion.of_injective I R
    have hi := congrArg (fun x ↦ e x i) h
    simpa [e, AdicCompletion.pi, AdicCompletion.map_of] using hi
  · intro x
    choose f hf using (fun i : ι ↦ AdicCompletion.of_surjective I R (e x i))
    refine ⟨f, e.injective ?_⟩
    funext i
    change AdicCompletion.map I (LinearMap.proj i) (AdicCompletion.of I (ι → R) f) = e x i
    rw [AdicCompletion.map_of]
    exact hf i

/-- A module with a finite basis over an adically complete ring is complete. -/
theorem isAdicComplete_of_finite_basis
    {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {ι : Type w} [Fintype ι] (b : Module.Basis ι R M) : IsAdicComplete I M := by
  have := isAdicComplete_finite_pi I ι
  exact isAdicComplete_of_linearEquiv I b.equivFun.symm

end AllCharacteristics
