import PfaffianDescent.HyperplaneParametrization
import PfaffianDescent.IndependentLinearPlaneQuarticDescent
import AllCharacteristics.FiniteFieldCubicPoint

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every field: the SAME actual coplanar degree-four closed point gives a
section of its original cubic surface by conic interpolation/complement/secant
or, over finite fields, Chevalley--Warning. No Chapter 3 theorem is used. -/
theorem cubic_coplanar_degree_four_independent_conic_secant_descent
    {K : Type u} [Field K]
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (x : closedPoints (hypersurface f hf))
    (hx : (hypersurfaceToBase f hf).residueDegree x.1 = 4)
    (c : Fin 4 → K) (hc : c ≠ 0)
    (hplane : Ideal.Quotient.mk (equationIdeal f hf).toIdeal (homogeneousLinearForm c) ∈
      x.1.asHomogeneousIdeal.toIdeal) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf,
      s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  classical
  rcases finite_or_infinite K with hfinite | hinfinite
  · letI : Finite K := hfinite
    exact finite_field_cubic_has_rational_section f hf
  · letI : Infinite K := hinfinite
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      push Not at h
      exact hc (funext h)
    apply linear_plane_section_degree_four_conic_secant_descent (hyperplaneInclusion c i)
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
