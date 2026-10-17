import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Algebra.Module.Submodule.Ker

/-! SOURCE ONLY / UNVERIFIED163. Pure bounded target normalization and
kernel/image identities. No geometric quotient or comparison input. -/
noncomputable section
namespace PfaffianDescent
universe u

/-- Choose the scalar identification from the actual one-dimensional
hypothesis. No target equivalence or finite-dimensionality is supplied. -/
def oneDimensionalQuotientTargetEquiv
    (L : Type u) [Field L] (N : Type u) [AddCommGroup N] [Module L N]
    (hN : Module.finrank L N = 1) : N ≃ₗ[L] L := by
  letI : Module.Finite L N := FiniteDimensional.of_finrank_pos (by rw [hN]; decide)
  exact LinearEquiv.ofFinrankEq N L (hN.trans (CommSemiring.finrank_self L).symm)

/-- An injective target change retains the EXACT original kernel. -/
lemma linearMap_kernel_postcomp_injective163
    {K M N W : Type u} [Field K]
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup W] [Module K W]
    (t : M →ₗ[K] N) (f : N →ₗ[K] W) (hf : Function.Injective f) :
    LinearMap.ker (f.comp t) = LinearMap.ker t := by
  ext x
  change f (t x) = 0 ↔ t x = 0
  constructor
  · intro h
    exact hf (h.trans f.map_zero.symm)
  · intro h
    rw [h, f.map_zero]

/-- The genuine H0 inclusion has range equal to the kernel whenever its
actual kernel equivalence has the proved sheaf square. -/
lemma linearMap_range_eq_kernel_of_equiv_square163
    {K U V W : Type u} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (t : V →ₗ[K] W) (j : U →ₗ[K] V) (e : U ≃ₗ[K] LinearMap.ker t)
    (hsquare : ∀ s, (e s).val = j s) :
    LinearMap.range j = LinearMap.ker t := by
  ext v
  change (∃ s, j s = v) ↔ t v = 0
  constructor
  · rintro ⟨s, rfl⟩
    rw [← hsquare s]
    exact (e s).property
  · intro hv
    refine ⟨e.symm ⟨v, hv⟩, ?_⟩
    rw [← hsquare]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)

end PfaffianDescent
