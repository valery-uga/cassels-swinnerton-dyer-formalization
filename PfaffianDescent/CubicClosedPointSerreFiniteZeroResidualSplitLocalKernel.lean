import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
open IsLocalRing
namespace PfaffianDescent

theorem cubicClosedPointSerreFiniteZeroResidual_splitLocal_kernel_eq_bot
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing R] [IsLocalRing A] [IsNoetherianRing A]
    (q : A →ₐ[R] R) [IsLocalHom q.toRingHom]
    (hm : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A) :
    RingHom.ker q.toRingHom = ⊥ := by
  let P : Ideal A := RingHom.ker q.toRingHom
  let t : A →ₗ[R] A := LinearMap.id - (Algebra.linearMap R A).comp q.toLinearMap
  have ht (a : A) : t a = a - algebraMap R A (q a) := rfl
  have hr : LinearMap.range t = P.restrictScalars R := by
    ext a
    constructor
    · rintro ⟨b, rfl⟩
      change q (t b) = 0
      simp [ht]
    · intro ha
      refine ⟨a, ?_⟩
      change q a = 0 at ha
      simp [ht, ha]
  have hle : P ≤ (maximalIdeal A) • P := by
    intro a ha
    have ham : a ∈ maximalIdeal A := by
      change q a = 0 at ha
      rw [← IsLocalRing.maximalIdeal_comap q.toRingHom]
      change q a ∈ maximalIdeal R
      rw [ha]
      exact (maximalIdeal R).zero_mem
    have hmap : a ∈ ((maximalIdeal A).restrictScalars R).map t := by
      refine ⟨a, ham, ?_⟩
      change q a = 0 at ha
      simp [ht, ha]
    rw [← hm, ← Ideal.smul_top_eq_map, Submodule.map_smul'', Submodule.map_top,
      hr, ← Ideal.smul_restrictScalars, hm] at hmap
    exact hmap
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (maximalIdeal A) P (IsNoetherian.noetherian P) hle
    (by rw [IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal A) bot_ne_top])

theorem cubicClosedPointSerreFiniteZeroResidual_splitLocal_etale_of_field_fiber
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing R] [IsLocalRing A] [IsNoetherianRing A]
    (q : A →ₐ[R] R) [IsLocalHom q.toRingHom]
    (hf : IsField (A ⧸ (maximalIdeal R).map (algebraMap R A))) :
    Algebra.Etale R A := by
  have hm : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A := by
    apply IsLocalRing.eq_maximalIdeal
    exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hf
  have hk := cubicClosedPointSerreFiniteZeroResidual_splitLocal_kernel_eq_bot q hm
  have hi : Function.Injective q := (RingHom.injective_iff_ker_eq_bot q.toRingHom).mpr hk
  have hs : Function.Surjective q := fun r => ⟨algebraMap R A r, q.commutes r⟩
  let e := AlgEquiv.ofBijective q ⟨hi, hs⟩
  exact Algebra.Etale.of_equiv e.symm

end PfaffianDescent
