import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The explicit dimension bound in Section 4, before choosing an
annihilating functional. Source draft; acceptance is recorded separately. -/
namespace PfaffianDescent.QuarticNet

/-- The annihilator of a map from a six-dimensional space into an
eight-dimensional space has dimension at least two. -/
theorem dualMap_kernel_finrank_at_least_two
    {K E V : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (φ : V →ₗ[K] E) (hE : Module.finrank K E = 8)
    (hV : Module.finrank K V = 6) :
    2 ≤ Module.finrank K (LinearMap.ker φ.dualMap) := by
  have hr := φ.dualMap.finrank_range_add_finrank_ker
  have hb := (LinearMap.range φ.dualMap).finrank_le
  have hEd : Module.finrank K (E →ₗ[K] K) = 8 := by
    exact Subspace.dual_finrank_eq.trans hE
  have hVd : Module.finrank K (V →ₗ[K] K) = 6 := by
    exact Subspace.dual_finrank_eq.trans hV
  rw [hEd] at hr
  rw [hVd] at hb
  omega

end PfaffianDescent.QuarticNet
