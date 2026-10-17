import PfaffianDescent.VoisinProjectiveVectorSchemePoint

/-!
# The actual affine chart map of a normalized projective vector point

This retains the ring homomorphism into the ground field used by the
projective point constructor, so selected-fiber coordinate sections can
be compared with the original normalized vectors.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable def projectiveVectorSchemePointInLinearChartMap
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (c v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (hcv : (homogeneousLinearForm c).eval v ≠ 0) :
    Away (grading I)
      (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)) →+* K := by
  let w := normalizedVectorInLinearChart c v
  have hwzero := normalizedVectorInLinearChart_zero I c v hv
  have hwone := normalizedVectorInLinearChart_eval_one c v hcv
  let z : CoordinateRing I :=
    Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c)
  have hz : z ∈ grading I 1 := polynomial_class_mem_grading I
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  have he : ∀ p ∈ I.toIdeal,
      (eval₂Hom (algebraMap K K) w) p = 0 := by
    intro p hp
    simpa using hwzero p hp
  have hOne :
      (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K K) w) he) z = 1 := by
    change (eval₂Hom (algebraMap K K) w) (homogeneousLinearForm c) = 1
    simpa using hwone
  exact linearNormalizedPointChartMapAt I w he z hz hOne

/-- The selected vector point is the chart map followed by the open
immersion of the affine Proj chart. -/
theorem projectiveVectorSchemePointInLinearChart_eq_chartMap
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (c v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (hcv : (homogeneousLinearForm c).eval v ≠ 0) :
    projectiveVectorSchemePointInLinearChart I c v hv hcv =
      Spec.map (CommRingCat.ofHom
        (projectiveVectorSchemePointInLinearChartMap I c v hv hcv)) ≫
        Proj.awayι (grading I)
          (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))
          (polynomial_class_mem_grading I
            (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c))
          (by decide : 0 < 1) := by
  rfl

/-- The affine chart ring map recovers the coordinates of the vector after
normalization by the chosen linear form. -/
theorem projectiveVectorSchemePointInLinearChartMap_coordinate
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (c v : Fin 4 → K)
    (hv : ∀ p ∈ I.toIdeal, p.eval v = 0)
    (hcv : (homogeneousLinearForm c).eval v ≠ 0)
    (j : Fin 4) :
    projectiveVectorSchemePointInLinearChartMap I c v hv hcv
      (linearChartCoordinate I
        (Ideal.Quotient.mk I.toIdeal (homogeneousLinearForm c))
        (polynomial_class_mem_grading I
          (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)) j) =
      normalizedVectorInLinearChart c v j := by
  unfold projectiveVectorSchemePointInLinearChartMap
  exact linearNormalizedPointChartMapAt_coordinate I
    (normalizedVectorInLinearChart c v) _ _ _ _ j

end PfaffianDescent
