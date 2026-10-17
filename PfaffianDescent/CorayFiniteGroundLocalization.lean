import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Localization cannot enlarge finite ground dimension

The image of an actual localization map has finite ground dimension. Every
denominator acts injectively on that image, hence surjectively. This supplies
an original preimage for each localized element, with no surjectivity premise.

Source draft: production and dependency audits are pending.
-/

noncomputable section
namespace PfaffianDescent.Coray

variable {K R N L : Type*} [Field K] [CommRing R] [Algebra K R]
  [AddCommGroup N] [AddCommGroup L] [Module R N] [Module R L]
  [Module K N] [Module K L] [IsScalarTower K R N] [IsScalarTower K R L]
  [Module.Finite K N]

include K

/-- A genuine localization of a finite-dimensional ground module is a
quotient of that original module even if denominator actions have kernels. -/
theorem groundFinite_localization_surjective
    (S : Submonoid R) (f : N →ₗ[R] L) [IsLocalizedModule S f] :
    Function.Surjective f := by
  let g : N →ₗ[K] L := f.restrictScalars K
  let V := LinearMap.range g
  intro y
  obtain ⟨⟨x, s⟩, hxy⟩ := IsLocalizedModule.surj S f y
  let e : V →ₗ[K] V :=
    { toFun := fun v => ⟨(s : R) • v.1, by
        obtain ⟨a, ha⟩ := v.2
        change f a = v.1 at ha
        refine ⟨(s : R) • a, ?_⟩
        change f ((s : R) • a) = (s : R) • v.1
        rw [f.map_smul, ha]⟩
      map_add' := fun v w => Subtype.ext (smul_add (s : R) v.1 w.1)
      map_smul' := fun k v => Subtype.ext (smul_comm (s : R) k v.1) }
  have he : Function.Injective e := by
    intro v w hvw
    apply Subtype.ext
    apply IsLocalizedModule.smul_injective f s
    exact congrArg Subtype.val hvw
  have hsurj : Function.Surjective e := LinearMap.surjective_of_injective he
  obtain ⟨v, hv⟩ := hsurj ⟨f x, ⟨x, rfl⟩⟩
  have hvy : v.1 = y := by
    apply IsLocalizedModule.smul_injective f s
    exact (congrArg Subtype.val hv).trans hxy.symm
  obtain ⟨a, ha⟩ := v.2
  exact ⟨a, ha.trans hvy⟩

/-- Ground finiteness is constructed for the actual localization; its
ground dimension is bounded by that of the original module. -/
theorem groundFinite_localization_finite_and_finrank_le
    (S : Submonoid R) (f : N →ₗ[R] L) [IsLocalizedModule S f] :
    Module.Finite K L ∧ Module.finrank K L ≤ Module.finrank K N := by
  have hf := groundFinite_localization_surjective (K := K) S f
  let g : N →ₗ[K] L := f.restrictScalars K
  letI : Module.Finite K L := Module.Finite.of_surjective g hf
  exact ⟨inferInstance, LinearMap.finrank_le_finrank_of_surjective (f := g) hf⟩

end PfaffianDescent.Coray
