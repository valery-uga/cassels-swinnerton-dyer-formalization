import PfaffianDescent.PlaneCubicConicDescent

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u

/-- The elementary conic proof for an actual closed point of residue degree
five on an actual projective plane cubic over an infinite field. -/
theorem plane_cubic_residue_degree_five_conic_descent
    {K : Type u} [Field K] [Infinite K]
    (f : MvPolynomial (Fin 3) K) (hf : f.IsHomogeneous 3)
    (x : closedPoints (hypersurface f hf))
    (hx : (hypersurfaceToBase f hf).residueDegree x.1 = 5) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase f hf) x.1
  have := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase f hf) x
  have hi : IsClosedImmersion ((hypersurface f hf).fromSpecResidueField x.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp x.2
  have hd := (AllCharacteristics.closedPoint_finrank_eq_residueDegree
    (hypersurfaceToBase f hf) x).trans hx
  exact plane_cubic_closed_point_conic_descent f hf hd
    ((hypersurface f hf).fromSpecResidueField x.1)
    (AllCharacteristics.pointAlgebra_spec (hypersurfaceToBase f hf) x.1).symm

end PfaffianDescent
