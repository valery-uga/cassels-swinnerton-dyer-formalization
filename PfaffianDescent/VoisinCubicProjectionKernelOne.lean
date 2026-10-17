import PfaffianDescent.CubicSurfaceSectionDimensions
import PfaffianDescent.CubicSurfacePointEvaluation

namespace PfaffianDescent

open MvPolynomial Module
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The only cubic relation in the homogeneous coordinate ring of a nonzero
cubic surface is a scalar multiple of its defining equation. -/
theorem cubicSurfaceHomogeneousCoordinateProjection_kernel_finrank_one
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hne : p ≠ 0) :
    finrank K (LinearMap.ker
      (cubicSurfaceHomogeneousCoordinateProjection p hp 3)) = 1 := by
  have heq : LinearMap.ker (cubicSurfaceHomogeneousCoordinateProjection p hp 3) =
      LinearMap.ker (cubicSurfaceProjection p hp 3) := by
    ext q
    constructor
    · intro h
      apply LinearMap.mem_ker.mpr
      exact congrArg Subtype.val (LinearMap.mem_ker.mp h)
    · intro h
      apply LinearMap.mem_ker.mpr
      exact Subtype.ext (LinearMap.mem_ker.mp h)
  rw [heq]
  have hkernel : LinearMap.range (cubicSurfaceRelation p hp 0) =
      LinearMap.ker (cubicSurfaceProjection p hp 3) := by
    simpa only [zero_add] using
      (cubicSurfaceRelation_range_eq_projection_ker p hp hne 0)
  rw [← hkernel,
    LinearMap.finrank_range_of_inj
      (cubicSurfaceRelation_injective p hp hne 0),
    four_variable_homogeneous_finrank]
  decide

end PfaffianDescent
