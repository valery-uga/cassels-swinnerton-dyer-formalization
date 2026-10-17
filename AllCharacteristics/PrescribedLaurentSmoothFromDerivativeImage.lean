import AllCharacteristics.CubicPencilSmoothFromDerivativeImage
import AllCharacteristics.LaurentPencilGenericCubic

/-! SOURCE ONLY / UNVERIFIED. Optional last adapter to the actual prescribed
Laurent equation in the frozen15-leaf tree. It does not modify that tree. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry
open HomogeneousProjective
universe u
variable {k : Type u} [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem prescribedLaurentGenericEquation_smooth_via_derivative_image
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hg0 : g ≠ 0)
    [Smooth (hypersurfaceToBase g hg)] :
    Smooth (hypersurfaceToBase (prescribedLaurentGenericEquation p g)
      (prescribedLaurentGenericEquation_homogeneous hp hg)) := by
  have h := cubicPencil_map_smooth_via_projective_derivative_image
    (polynomialToLaurentCoefficientMap (k := k))
    polynomialToLaurentCoefficientMap_injective p g hp hg hg0
  simpa only [prescribedLaurentGenericEquation, prescribedPowerSeriesPencil,
    MvPolynomial.map_map, polynomialToLaurentCoefficientMap] using h

end AllCharacteristics
