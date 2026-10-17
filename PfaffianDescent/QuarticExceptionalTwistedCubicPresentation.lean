import PfaffianDescent.QuarticExceptionalTwistedCubicPoint
import PfaffianDescent.QuarticTwistedCubicGeometricPresentation

/-!
# Ground presentation of the exceptional twisted cubic

The exceptional tangent-net base curve is not only known to contain a rational
point: its explicit ground-field coordinate change identifies its homogeneous
ideal with the standard twisted-cubic ideal.
-/

namespace PfaffianDescent.QuarticNet

open MvPolynomial
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K]

/-- In the exceptional full-support branch, the homogeneous ideal of the
base curve is a ground-coordinate presentation of the standard twisted cubic.
This is the embedded conclusion of the base-locus alternative, not merely its
rational-point consequence. -/
theorem exceptionalTwistedCubic_groundPresentation
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0) :
    GroundTwistedCubicPresentation
      (exceptionalTwistedCubicHomogeneousIdeal a b c d e f) := by
  have hbe : b * e - c * d ≠ 0 :=
    baseLocus_be_sub_cd_ne_zero_of_delta_zero a b c d e f hb hc hd he hdelta
  have hdet : (baseLocusCubicCoefficientMatrix a b c d e).det ≠ 0 :=
    baseLocusCubicCoefficientMatrix_det_ne_zero a b c d e ha hb hc hd he hbe
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
    (baseLocusCubicCoefficientMatrix a b c d e) hdet, ?_⟩
  change (Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f))).map
    (linearSubstitution (baseLocusCubicCoefficientMatrix a b c d e)).toRingHom =
      standardTwistedCubicIdeal K
  exact exceptionalTwistedCubic_ideal_map_eq_standard
    a b c d e f ha hb hc hd he hdelta

end PfaffianDescent.QuarticNet
