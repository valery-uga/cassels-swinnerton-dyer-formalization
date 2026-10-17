import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Surjectivity of finite local algebra maps from their residue maps

Nakayama's lemma detects surjectivity when the maximal ideal of the target
is extended from the base. This criterion retains inseparable residue fields.
-/

open IsLocalRing
namespace AllCharacteristics
universe u v w t

/-- A map to a finite algebra is surjective if it is surjective after a residue
map whose kernel is the extended maximal ideal of the local base. -/
theorem algHom_surjective_of_residue_surjective
    {R : Type u} {B : Type v} {A : Type w} {L : Type t}
    [CommRing R] [IsLocalRing R] [CommRing B] [CommRing A] [CommRing L]
    [Algebra R B] [Algebra R A] [Module.Finite R A]
    (g : B →ₐ[R] A) (c : A →+* L)
    (hker : RingHom.ker c = (maximalIdeal R).map (algebraMap R A))
    (h : Function.Surjective (c.comp g.toRingHom)) : Function.Surjective g := by
  change Function.Surjective g.toLinearMap
  rw [← LinearMap.range_eq_top, ← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  intro a _
  obtain ⟨b, hb⟩ := h (c a)
  rw [Ideal.smul_top_eq_map]
  refine Submodule.mem_sup.mpr ⟨g b, ⟨b, rfl⟩, a - g b, ?_, by simp⟩
  change a - g b ∈ (maximalIdeal R).map (algebraMap R A)
  rw [← hker, RingHom.mem_ker, map_sub]
  exact sub_eq_zero.mpr hb.symm

/-- For a finite local algebra with extended maximal ideal, a map is
surjective as soon as its composite with the presented residue field is. -/
theorem algHom_surjective_of_local_residue_surjective
    {R : Type u} {B : Type v} {A : Type w} {L : Type t}
    [CommRing R] [IsLocalRing R] [CommRing B] [CommRing A] [Field L]
    [Algebra R B] [Algebra R A] [Module.Finite R A] [IsLocalRing A]
    (g : B →ₐ[R] A) (c : A →+* L) (hc : Function.Surjective c)
    (hmax : maximalIdeal A = (maximalIdeal R).map (algebraMap R A))
    (h : Function.Surjective (c.comp g.toRingHom)) : Function.Surjective g :=
  algHom_surjective_of_residue_surjective g c
    ((IsLocalRing.ker_eq_maximalIdeal c hc).trans hmax) h

end AllCharacteristics
