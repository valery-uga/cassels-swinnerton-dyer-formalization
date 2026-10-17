import PfaffianDescent.OneDimensionalQuotientTargetIso
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! SOURCE ONLY / UNVERIFIED. Normalize a quotient onto an arbitrary actual
one-dimensional target without taking a chosen target trivialization as a
premise. Actual target isomorphism is precisely the existing field-target
quotient relation after normalization. -/
noncomputable section
namespace PfaffianDescent
universe u

/-- A target identification is derived from its literal dimension-one
hypothesis. No basis, nonzero vector or identification is supplied. -/
def oneDimensionalTargetEquivField
    (L N : Type u) [Field L] [AddCommGroup N] [Module L N]
    (hN : Module.finrank L N = 1) : N ≃ₗ[L] L :=
  (Classical.choice
    (Module.nonempty_linearEquiv_of_finrank_eq_one (R := L) (M := N) hN)).symm

def normalizeOneDimensionalQuotient
    {L M N : Type u} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] (hN : Module.finrank L N = 1)
    (q : M →ₗ[L] N) : M →ₗ[L] L :=
  (oneDimensionalTargetEquivField L N hN).toLinearMap.comp q

theorem normalizeOneDimensionalQuotient_surjective
    {L M N : Type u} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] (hN : Module.finrank L N = 1)
    (q : M →ₗ[L] N) (hq : Function.Surjective q) :
    Function.Surjective (normalizeOneDimensionalQuotient hN q) :=
  (oneDimensionalTargetEquivField L N hN).surjective.comp hq

/-- Changing a target identification changes the normalized functional
only by an actual automorphism of the residue-field target. -/
theorem oneDimensionalQuotient_normalizations_targetIso
    {L M N : Type u} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] (q : M →ₗ[L] N)
    (e₁ e₂ : N ≃ₗ[L] L) :
    OneDimensionalQuotientTargetIso
      (e₁.toLinearMap.comp q) (e₂.toLinearMap.comp q) := by
  refine ⟨e₁.symm.trans e₂, ?_⟩
  ext x
  change e₂ (q x) = e₂ (e₁.symm (e₁ (q x)))
  rw [e₁.symm_apply_apply]

theorem normalizeOneDimensionalQuotient_reverse
    {L M N : Type u} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] (hN : Module.finrank L N = 1)
    (ell : M →ₗ[L] L) :
    normalizeOneDimensionalQuotient hN
      ((oneDimensionalTargetEquivField L N hN).symm.toLinearMap.comp ell) = ell := by
  ext x
  change (oneDimensionalTargetEquivField L N hN)
    ((oneDimensionalTargetEquivField L N hN).symm (ell x)) = ell x
  exact (oneDimensionalTargetEquivField L N hN).apply_symm_apply (ell x)

/-- Isomorphism of the actual arbitrary targets, commuting with their
quotient maps, is exactly the field-target equivalence after normalization. -/
theorem normalizedOneDimensionalQuotients_targetIso_iff
    {L M N₁ N₂ : Type u} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N₁] [Module L N₁] [AddCommGroup N₂] [Module L N₂]
    (hN₁ : Module.finrank L N₁ = 1) (hN₂ : Module.finrank L N₂ = 1)
    (q₁ : M →ₗ[L] N₁) (q₂ : M →ₗ[L] N₂) :
    OneDimensionalQuotientTargetIso
      (normalizeOneDimensionalQuotient hN₁ q₁)
      (normalizeOneDimensionalQuotient hN₂ q₂) ↔
      ∃ e : N₁ ≃ₗ[L] N₂, q₂ = e.toLinearMap.comp q₁ := by
  let e₁ := oneDimensionalTargetEquivField L N₁ hN₁
  let e₂ := oneDimensionalTargetEquivField L N₂ hN₂
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨(e₁.trans d).trans e₂.symm, ?_⟩
    ext x
    have hx := LinearMap.congr_fun hd x
    change e₂ (q₂ x) = d (e₁ (q₁ x)) at hx
    change q₂ x = e₂.symm (d (e₁ (q₁ x)))
    simpa only [e₂.symm_apply_apply] using congrArg e₂.symm hx
  · rintro ⟨e, he⟩
    refine ⟨(e₁.symm.trans e).trans e₂, ?_⟩
    ext x
    have hx := LinearMap.congr_fun he x
    change q₂ x = e (q₁ x) at hx
    change e₂ (q₂ x) = e₂ (e (e₁.symm (e₁ (q₁ x))))
    rw [hx, e₁.symm_apply_apply]

end PfaffianDescent
