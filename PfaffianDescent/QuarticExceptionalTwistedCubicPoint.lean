import PfaffianDescent.QuarticTwistedCubicPoint
import PfaffianDescent.QuarticExceptionalBaseLocus

/-!
# Rational point of the exceptional twisted cubic

The exceptional full-support base curve is an invertible ground-field linear
image of the standard twisted cubic.  This file turns that ideal comparison
into an actual section of the projective curve.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable {K : Type u} [Field K]

/-- The three exceptional quadrics, viewed as the homogeneous ideal of their
projective base curve. -/
noncomputable def exceptionalTwistedCubicHomogeneousIdeal (a b c d e f : K) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
  ⟨Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f)),
    Ideal.homogeneous_span _ _ (by
      intro q hq
      obtain ⟨i, rfl⟩ := hq
      exact ⟨2, scaledBaseLocusQuadricPolynomials_homogeneous a b c d e f i⟩)⟩

/-- In the full-support exceptional branch, the explicit base twisted cubic
has a rational section over the ground field. -/
theorem exceptionalTwistedCubic_has_rational_section
    (a b c d e f : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (he : e ≠ 0)
    (hdelta : baseLocusDelta a b c d e f = 0) :
    ∃ s : Spec (.of K) ⟶ scheme (exceptionalTwistedCubicHomogeneousIdeal a b c d e f),
      s ≫ toBase (exceptionalTwistedCubicHomogeneousIdeal a b c d e f) = 𝟙 _ := by
  let M := baseLocusCubicCoefficientMatrix a b c d e
  have hbe : b * e - c * d ≠ 0 :=
    baseLocus_be_sub_cd_ne_zero_of_delta_zero a b c d e f hb hc hd he hdelta
  have hM : IsUnit M.det := isUnit_iff_ne_zero.mpr
    (baseLocusCubicCoefficientMatrix_det_ne_zero a b c d e ha hb hc hd he hbe)
  apply splitTwistedCubic_has_rational_section
    (exceptionalTwistedCubicHomogeneousIdeal a b c d e f) M hM
  change (Ideal.span (Set.range (scaledBaseLocusQuadricPolynomials a b c d e f))).map
    (linearSubstitution M).toRingHom = standardTwistedCubicIdeal K
  exact exceptionalTwistedCubic_ideal_map_eq_standard a b c d e f ha hb hc hd he hdelta

end QuarticNet
end PfaffianDescent
