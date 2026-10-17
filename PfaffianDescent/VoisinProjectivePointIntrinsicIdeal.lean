import PfaffianDescent.VoisinProjectivePointScale
import PfaffianDescent.VoisinIntrinsicQuadraticKernelIdeal

/-! Intrinsic eight-point ideals depend only on the marked projective points. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Two normalized eight-point vector families defining the same labeled
projective points have the same intrinsic cubic-plus-quadratic-kernel ideal.
The two normalizing linear forms may differ. -/
theorem intrinsicEightPointTripleHomogeneousIdeal_eq_of_projectivePointFamilies
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (p : MvPolynomial (Fin 4) F) (hp : p.IsHomogeneous 3)
    (x y : Fin 8 → Fin 4 → F)
    (ellx elly : MvPolynomial (Fin 4) K)
    (hellx : ellx.IsHomogeneous 1) (helly : elly.IsHomogeneous 1)
    (hxell : ∀ k, ellx.eval₂ (algebraMap K F) (x k) = 1)
    (hyell : ∀ k, elly.eval₂ (algebraMap K F) (y k) = 1)
    (hex : ∀ k, ∀ q ∈ I.toIdeal,
      q.eval₂ (algebraMap K F) (x k) = 0)
    (hey : ∀ k, ∀ q ∈ I.toIdeal,
      q.eval₂ (algebraMap K F) (y k) = 0)
    (hpoint : ∀ k,
      linearNormalizedPoint I (x k) ellx hellx (hxell k) (hex k) =
      linearNormalizedPoint I (y k) elly helly (hyell k) (hey k))
    (j : Fin 8 → Fin 4)
    (hxj : ∀ k, x k (j k) ≠ 0)
    (hyj : ∀ k, y k (j k) ≠ 0) :
    intrinsicEightPointTripleHomogeneousIdeal p hp y =
      intrinsicEightPointTripleHomogeneousIdeal p hp x := by
  let a : Fin 8 → F := fun k => y k (j k) / x k (j k)
  have ha : ∀ k, IsUnit (a k) := by
    intro k
    exact isUnit_iff_ne_zero.mpr (div_ne_zero (hyj k) (hxj k))
  have hscale : y = fun k l => a k * x k l := by
    funext k l
    exact linearNormalizedPoint_vectors_proportional
      I (x k) (y k) ellx elly hellx helly
      (hxell k) (hyell k) (hex k) (hey k)
      (hpoint k) (j k) (hxj k) (hyj k) l
  rw [hscale]
  simpa only [Equiv.refl_apply] using
    intrinsicEightPointTripleHomogeneousIdeal_scale_relabel
      p hp (Equiv.refl (Fin 8)) a ha x

end PfaffianDescent
