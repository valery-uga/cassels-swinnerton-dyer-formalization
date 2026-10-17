import PfaffianDescent.HyperplaneParametrization
import PfaffianDescent.LinearPlaneConicDescent

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The elementary conic/residual proof for a degree-five closed point lying
in any ground-field plane of the actual cubic surface. The plane parametrization,
closed point of the plane cubic, and rational section of the original surface
are all constructed from the nonzero linear equation. -/
theorem cubic_coplanar_degree_five_conic_descent
    {K : Type u} [Field K] [Infinite K]
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (x : closedPoints (hypersurface f hf))
    (hx : (hypersurfaceToBase f hf).residueDegree x.1 = 5)
    (c : Fin 4 → K) (hc : c ≠ 0)
    (hplane : Ideal.Quotient.mk (equationIdeal f hf).toIdeal (homogeneousLinearForm c) ∈
      x.1.asHomogeneousIdeal.toIdeal) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  apply linear_plane_section_degree_five_conic_descent (hyperplaneInclusion c i)
    (coordinateOmission i) (hyperplaneInclusion_leftInverse c i) f hf x hx
  apply (linearHypersurfaceSectionι_mem_range_iff (hyperplaneInclusion c i)
    (coordinateOmission i) (hyperplaneInclusion_leftInverse c i) f hf x.1).mpr
  intro k
  by_cases hk : k = i
  · subst k
    rw [hyperplaneInclusion_pivot_relation c i hi, map_mul]
    exact Ideal.mul_mem_left _ _ hplane
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    rw [hyperplaneInclusion_other_relation, map_zero]
    exact Ideal.zero_mem _

end PfaffianDescent
