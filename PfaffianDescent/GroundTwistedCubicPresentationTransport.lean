import PfaffianDescent.QuarticTwistedCubicGeometricPresentation

/-! Transport the embedded twisted-cubic conclusion through the actual
invertible coordinate substitution used to compare full quadratic systems. -/

namespace PfaffianDescent.QuarticNet

open MvPolynomial Matrix
open AllCharacteristics.HomogeneousProjective
open scoped MatrixGroups

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
variable {K : Type u} [Field K]

/-- If the actual coordinate image of an ideal is a twisted cubic, the
original ideal has the corresponding composed embedded presentation. -/
theorem GroundTwistedCubicPresentation.of_coordinate_image
    {I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)}
    (M : GL (Fin 4) K)
    (hIJ : I.toIdeal.map
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)).toRingHom = J.toIdeal)
    (hJ : GroundTwistedCubicPresentation J) :
    GroundTwistedCubicPresentation I := by
  obtain ⟨N, hN⟩ := hJ
  refine ⟨M * N, ?_⟩
  change I.toIdeal.map
    (linearSubstitution ((M : Matrix (Fin 4) (Fin 4) K) *
      (N : Matrix (Fin 4) (Fin 4) K))).toRingHom = standardTwistedCubicIdeal K
  rw [← linearSubstitution_comp]
  change I.toIdeal.map
    ((linearSubstitution (N : Matrix (Fin 4) (Fin 4) K)).toRingHom.comp
      (linearSubstitution (M : Matrix (Fin 4) (Fin 4) K)).toRingHom) = _
  rw [← Ideal.map_map, hIJ]
  exact hN

end PfaffianDescent.QuarticNet
