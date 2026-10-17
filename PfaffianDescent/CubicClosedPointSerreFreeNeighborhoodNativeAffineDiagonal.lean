import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodCover

/-! # Affine intersections for the actual cubic free cover -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual projective cubic has an affine absolute diagonal, so the
constructed affine free neighborhoods have affine pairwise intersections. -/
theorem cubicClosedPointSerreFreeNeighborhood_native_affine_diagonal
    (K : Type u) [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    IsAffineHom (pullback.diagonal (terminal.from (hypersurface p hp))) := by
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  have h : IsSeparated (hypersurfaceToBase p hp ≫ terminal.from (Spec (.of K))) :=
    inferInstance
  rw [terminal.comp_from] at h
  letI := h
  infer_instance

end PfaffianDescent.ProjectiveNegativeTwist
