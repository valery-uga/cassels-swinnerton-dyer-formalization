import Mathlib.RingTheory.Flat.IsBaseChange

/-!
# Kernels in flat pushout squares of algebras

The canonical map on kernels is a base change along the flat horizontal map.
This is the exactness input used to compare cotangent homology.
-/

open Algebra
namespace AllCharacteristics
universe u v w z
variable (A : Type u) (B : Type v) (C : Type w) (D : Type z)
variable [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Algebra A B] [Algebra A C] [Algebra A D] [Algebra B D] [Algebra C D]
variable [IsScalarTower A B D] [IsScalarTower A C D]

/-- The original coefficient map restricted to the kernels of the vertical maps. -/
def algebraKernelMap :
    RingHom.ker (algebraMap A C) →ₗ[A] RingHom.ker (algebraMap B D) where
  toFun x := ⟨algebraMap A B x, by
    rw [RingHom.mem_ker, ← IsScalarTower.algebraMap_apply A B D,
      IsScalarTower.algebraMap_apply A C D, show algebraMap A C x = 0 from x.2, map_zero]⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' r x := by
    apply Subtype.ext
    simp [Algebra.smul_def]

/-- Flat base change preserves the actual kernel in a pushout square. -/
lemma flatPushout_kernel_isBaseChange [Module.Flat A B] [Algebra.IsPushout A B C D] :
    IsBaseChange B (algebraKernelMap A B C D) := by
  apply IsBaseChange.of_left_exact B (algebraKernelMap A B C D)
    (Algebra.linearMap A B) (IsScalarTower.toAlgHom A C D).toLinearMap
    (f := (RingHom.ker (algebraMap A C)).subtype) (g := Algebra.linearMap A C)
    (f' := (RingHom.ker (algebraMap B D)).subtype) (g' := Algebra.linearMap B D)
  · rfl
  · apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, Algebra.linearMap_apply, AlgHom.toLinearMap_apply,
      IsScalarTower.coe_toAlgHom', LinearMap.restrictScalars_apply,
      ← IsScalarTower.algebraMap_apply]
  · exact IsBaseChange.linearMap A B
  · exact Algebra.IsPushout.out
  · exact (Algebra.linearMap A C).exact_subtype_ker_map
  · exact Subtype.val_injective
  · exact (Algebra.linearMap B D).exact_subtype_ker_map
  · exact Subtype.val_injective

end AllCharacteristics
