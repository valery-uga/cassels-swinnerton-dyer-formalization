import PfaffianDescent.LinearHypersurfaceSection
import PfaffianDescent.ClosedImmersionPointLift
import PfaffianDescent.PlaneCubicClosedPoint

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u

/-- The conic/residual construction for an actual degree-five closed point
in an actual plane section of a cubic surface. The plane is parametrized by
any split linear inclusion, and the resulting rational section lies on the
original cubic surface. -/
theorem linear_plane_section_degree_five_conic_descent
    {K : Type u} [Field K] [Infinite K]
    (M : Matrix (Fin 4) (Fin 3) K) (N : Matrix (Fin 3) (Fin 4) K) (hNM : N*M = 1)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (x : closedPoints (hypersurface f hf))
    (hx : (hypersurfaceToBase f hf).residueDegree x.1 = 5)
    (hplane : x.1 ∈ Set.range (linearHypersurfaceSectionι M N hNM f hf)) :
    ∃ s : Spec (.of K) ⟶ hypersurface f hf, s ≫ hypersurfaceToBase f hf = 𝟙 _ := by
  let j := linearHypersurfaceSectionι M N hNM f hf
  have : IsClosedImmersion j :=
    inferInstanceAs (IsClosedImmersion (linearHypersurfaceSectionι M N hNM f hf))
  obtain ⟨y, _, hy⟩ := closedImmersion_closedPoint_lift j (hypersurfaceToBase f hf) x hplane
  have he : j ≫ hypersurfaceToBase f hf = hypersurfaceToBase (rectangularSubstitution M f)
      (rectangularSubstitution_homogeneous M hf) := linearHypersurfaceSectionι_toBase M N hNM f hf
  rw [he] at hy
  obtain ⟨s, hs⟩ := plane_cubic_residue_degree_five_conic_descent
    (rectangularSubstitution M f) (rectangularSubstitution_homogeneous M hf) y (hy.trans hx)
  refine ⟨s ≫ j, ?_⟩
  rw [Category.assoc, he, hs]

end PfaffianDescent
