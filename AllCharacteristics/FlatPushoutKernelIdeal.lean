import AllCharacteristics.FlatPushoutKernel

/-! # Kernel ideals under flat pushout

The kernel of the base-changed algebra map is the extension of the original
kernel ideal. This identifies the scheme-theoretic image on affine charts
after flat base change.
-/

open Algebra
open scoped TensorProduct
namespace AllCharacteristics
universe u v w z
variable (A : Type u) (B : Type v) (C : Type w) (D : Type z)
variable [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
variable [IsScalarTower A B D] [IsScalarTower A C D]

/-- Flat base change in a pushout carries the original kernel ideal to
exactly the new kernel ideal. -/
lemma flatPushout_map_kernel [Module.Flat A B] [Algebra.IsPushout A B C D] :
    (RingHom.ker (algebraMap A C)).map (algebraMap A B) =
      RingHom.ker (algebraMap B D) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change algebraMap B D (algebraMap A B a) = 0
    rw [← IsScalarTower.algebraMap_apply A B D, IsScalarTower.algebraMap_apply A C D,
      show algebraMap A C a = 0 from ha, map_zero]
  · let h := flatPushout_kernel_isBaseChange A B C D
    have hm : ∀ t : B ⊗[A] RingHom.ker (algebraMap A C),
        (h.equiv t : B) ∈ (RingHom.ker (algebraMap A C)).map (algebraMap A B) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul b a =>
        change b * algebraMap A B a.val ∈ (RingHom.ker (algebraMap A C)).map (algebraMap A B)
        exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ a.property)
      | add x y hx hy =>
        simpa only [map_add, Submodule.coe_add] using Ideal.add_mem _ hx hy
    intro b hb
    obtain ⟨t, ht⟩ := h.equiv.surjective ⟨b, hb⟩
    simpa only [ht] using hm t

end AllCharacteristics
