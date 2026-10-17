import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridKernelCoordinates

/-! Exact component coordinate ratios transport every native kernel section
to the ordered restriction kernel. -/
noncomputable section
open MvPolynomial Module
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_nativeCubicKernel_orderedTransport_of_componentRatios
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [Field L] [Algebra K L] {n : ℕ}
    (φ : Fin n → A →ₐ[K] L) (x : Fin 4 → A) (y : Fin n → Fin 4 → L)
    (hy : ∀ i, y i 0 = 1)
    (hratios : ∀ i j, (φ i (x 0))⁻¹ * φ i (x j) = y i j)
    (s : homogeneousSubmodule (Fin 4) K 3)
    (hs : s ∈ LinearMap.ker (homogeneousSectionRestriction x 3)) :
    voisinDegreeTenSelectedAvoidance_mapCubicSection (L := L) s ∈
      LinearMap.ker (homogeneousSectionRestriction (fun j i => y i j) 3) := by
  have hzero : ∀ i, s.1.eval₂ (algebraMap K L) (y i) = 0 := by
    intro i
    apply voisinDegreeTenSelectedAvoidance_homogeneous_zero_of_normalizedRatios
      s.1 s.2 (y i) (fun j => φ i (x j)) 0 (hy i)
    · intro j
      simpa only [hy i, inv_one, one_mul] using hratios i j
    · exact voisinDegreeTenSelectedAvoidance_nativeCubicKernel_eval_component (φ i) x s hs
  rw [LinearMap.mem_ker]
  funext i
  simpa [homogeneousSectionRestriction_apply, finite_product_evaluation_apply,
    voisinDegreeTenSelectedAvoidance_mapCubicSection, MvPolynomial.eval_map] using hzero i

end PfaffianDescent
