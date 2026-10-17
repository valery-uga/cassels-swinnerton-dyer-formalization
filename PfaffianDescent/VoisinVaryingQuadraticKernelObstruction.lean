import PfaffianDescent.VoisinQuadraticRestrictionKernelUniversalFamily

/-!
# Why a varying rank bound does not exclude the generic eight-point pencil

An eight-point configuration whose quadratic restriction kernel has rank two
itself determines a two-dimensional system of quadrics through those points.
Thus a dimension-at-most-eight incidence exclusion can apply to a fixed
ground-field system, but cannot apply to every system allowed to vary with
the configuration.
-/

namespace PfaffianDescent

open MvPolynomial Module

universe u

theorem exists_rank_two_varying_quadratic_system_through_datum
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (x : Fin 4 → A)
    (hker : finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)) = 2) :
    ∃ W : Submodule K (homogeneousSubmodule (Fin 4) K 2),
      finrank K W = 2 ∧
      (∀ s ∈ W, s.1.eval₂ (algebraMap K A) x = 0) ∧
      ∃ s : homogeneousSubmodule (Fin 4) K 2, s ∈ W ∧ s ≠ 0 := by
  let W := LinearMap.ker (homogeneousSectionRestriction (K := K) x 2)
  have hpos : 0 < finrank K W := by
    change 0 < finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 2))
    omega
  let i : Fin (finrank K W) := ⟨0, hpos⟩
  let s := quadraticRestrictionKernelFrame (K := K) x i
  have hsW : s ∈ W :=
    (quadraticRestrictionKernelBasis (K := K) x i).property
  have hs0 : s ≠ 0 :=
    (quadraticRestrictionKernelFrame_linearIndependent (K := K) x).ne_zero i
  refine ⟨W, hker, ?_, s, hsW, hs0⟩
  intro t ht
  have ht0 := LinearMap.mem_ker.mp ht
  simpa only [homogeneousSectionRestriction_apply] using ht0

end PfaffianDescent
