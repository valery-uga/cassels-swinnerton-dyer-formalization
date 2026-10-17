import PfaffianDescent.VoisinNormalizedPointAtCompatibility

/-! Intrinsic eight-point ideals from explicit normalized-chart points. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Equality of the actual marked projective points, expressed with chosen
degree-one chart elements, implies equality of the intrinsic ideals of
their normalized coordinate vectors. -/
theorem intrinsicEightPointTripleHomogeneousIdeal_eq_of_pointAtFamilies
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
      linearNormalizedPointAt I (x k) (hex k)
        (Ideal.Quotient.mk I.toIdeal ellx)
        (polynomial_class_mem_grading I ellx hellx) (hxell k) =
      linearNormalizedPointAt I (y k) (hey k)
        (Ideal.Quotient.mk I.toIdeal elly)
        (polynomial_class_mem_grading I elly helly) (hyell k))
    (j : Fin 8 → Fin 4)
    (hxj : ∀ k, x k (j k) ≠ 0)
    (hyj : ∀ k, y k (j k) ≠ 0) :
    intrinsicEightPointTripleHomogeneousIdeal p hp y =
      intrinsicEightPointTripleHomogeneousIdeal p hp x := by
  refine intrinsicEightPointTripleHomogeneousIdeal_eq_of_projectivePointFamilies
    I p hp x y ellx elly hellx helly hxell hyell hex hey ?_ j hxj hyj
  intro k
  rw [← linearNormalizedPointAt_mk_eq_linearNormalizedPoint
    I (x k) (hex k) ellx hellx (hxell k)]
  rw [← linearNormalizedPointAt_mk_eq_linearNormalizedPoint
    I (y k) (hey k) elly helly (hyell k)]
  exact hpoint k

end PfaffianDescent
