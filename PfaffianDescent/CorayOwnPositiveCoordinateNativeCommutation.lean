import PfaffianDescent.CorayOwnPositiveCoordinateCokernelHZero

/-! SOURCE ONLY. Native positive coordinate multiplications commute as whole
actual sheaf morphisms, providing the square for chart-frame cokernel transport. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- SAME original coordinates commute on every actual positive coefficient;
all points and all sections are retained, with no matrix-square certificate. -/
theorem ownPositiveCoordinateMultiplication_comm_native
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (j ell : Fin 4) (m : ℕ) :
    ownPositiveCoordinateMultiplication C j m ≫
        ownPositiveCoordinateMultiplication C ell (m + 1) =
      ownPositiveCoordinateMultiplication C ell m ≫
        ownPositiveCoordinateMultiplication C j (m + 1) := by
  ext U z
  apply Subtype.ext
  funext x
  change algebraMap (CoordinateRing C) (PositiveFiber (grading C) x.1) (coordinate C ell) *
      (algebraMap (CoordinateRing C) (PositiveFiber (grading C) x.1) (coordinate C j) * z.1 x) =
    algebraMap (CoordinateRing C) (PositiveFiber (grading C) x.1) (coordinate C j) *
      (algebraMap (CoordinateRing C) (PositiveFiber (grading C) x.1) (coordinate C ell) * z.1 x)
  ring

end PfaffianDescent.Coray
