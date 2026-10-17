import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridExtendedCurveContradiction
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridKernelScalarExtension

/-! Actual finite cubic witnesses exclude a common prime curve of the
ordered cubic restriction kernel. -/
noncomputable section
open AlgebraicGeometry MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_finiteTriple_cubicKernel_noFixedHeightTwoPrime
    {K : Type u} [Field K] {n : ℕ}
    (x : Fin n → Fin 4 → K) (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3) (hr : r.IsHomogeneous 3)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))]
    (hqzero : ∀ i, q.eval (x i) = 0) (hrzero : ∀ i, r.eval (x i) = 0) :
    ¬ ∃ C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
      C.toIdeal.IsPrime ∧ C.toIdeal.height = 2 ∧ p ∈ C.toIdeal ∧
      (∀ s : homogeneousSubmodule (Fin 4) K 3,
        s ∈ LinearMap.ker (homogeneousSectionRestriction
          (fun j i => x i j) 3) → s.1 ∈ C.toIdeal) := by
  rintro ⟨C, hCprime, hCheight, hpC, hcontains⟩
  have hqker : (⟨q, hq⟩ : homogeneousSubmodule (Fin 4) K 3) ∈
      LinearMap.ker (homogeneousSectionRestriction (fun j i => x i j) 3) := by
    rw [LinearMap.mem_ker]
    funext i
    simpa [homogeneousSectionRestriction_apply, finite_product_evaluation_apply] using hqzero i
  have hrker : (⟨r, hr⟩ : homogeneousSubmodule (Fin 4) K 3) ∈
      LinearMap.ker (homogeneousSectionRestriction (fun j i => x i j) 3) := by
    rw [LinearMap.mem_ker]
    funext i
    simpa [homogeneousSectionRestriction_apply, finite_product_evaluation_apply] using hrzero i
  exact voisinDegreeTenSelectedAvoidance_finiteTriple_not_contained_in_heightTwoPrime
    p q r hp hq hr C hCprime hCheight
      ⟨hpC, hcontains ⟨q, hq⟩ hqker, hcontains ⟨r, hr⟩ hrker⟩

end PfaffianDescent
