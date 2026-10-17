import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity

noncomputable section
namespace PfaffianDescent
universe u

/-- An injective linear map with exactly the restriction kernel as image
identifies its actual section space with that literal kernel. -/
def cubicClosedPointSerreSurfaceJetCotangent_exactKernelLinearEquiv
    {K V W A : Type u} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup A] [Module K A]
    (a : A →ₗ[K] V) (r : V →ₗ[K] W) (ha : Function.Injective a)
    (hz : ∀ s, r (a s) = 0)
    (hlift : ∀ v, r v = 0 → ∃ s, a s = v) : A ≃ₗ[K] r.ker :=
  LinearEquiv.ofBijective (a.codRestrict r.ker (fun s => hz s))
    ⟨fun s t h => ha (congrArg Subtype.val h), fun v => by
      obtain ⟨s, hs⟩ := hlift v.1 v.2
      exact ⟨s, Subtype.ext hs⟩⟩

/-- The actual section kernel has dimension eight when the restriction is
onto an eleven-dimensional target from nineteen global cubic sections. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_exactKernel_finrank_eight
    {K V W A : Type u} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup A] [Module K A] [FiniteDimensional K V] [FiniteDimensional K W]
    (a : A →ₗ[K] V) (r : V →ₗ[K] W) (ha : Function.Injective a)
    (hz : ∀ s, r (a s) = 0) (hlift : ∀ v, r v = 0 → ∃ s, a s = v)
    (hr : Function.Surjective r) (hV : Module.finrank K V = 19)
    (hW : Module.finrank K W = 11) : Module.finrank K A = 8 := by
  rw [(cubicClosedPointSerreSurfaceJetCotangent_exactKernelLinearEquiv a r ha hz hlift).finrank_eq]
  have h := LinearMap.finrank_range_add_finrank_ker r
  rw [LinearMap.range_eq_top.mpr hr, finrank_top, hV, hW] at h
  omega

end PfaffianDescent
