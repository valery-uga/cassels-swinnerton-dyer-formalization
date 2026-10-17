import PfaffianDescent.P3QuadraticLaurentMultiplication
import PfaffianDescent.VoisinP3TopCechExtComparison

/-! # Native residue coordinates evaluated against an arbitrary quadratic -/
noncomputable section
open AlgebraicGeometry MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentLocalization LaurentCechExact
universe u
variable (K : Type u) [Field K]

/-- The native raw residue dual is actual quadratic multiplication,
followed by the coefficient with four exponents minus one. -/
theorem p3NegativeSix_raw_residue_dual_eq_multiplication
    (w : P3RawTopCocycle K 6) :
    (p3QuadraticDualCoordinateEquiv K).symm (p3NegativeSixTopResidueCoordinates K w) =
      p3QuadraticLaurentResidueLinearMap K
        ((p3NegativeTwistCechTermToLaurent K 6 3 w.1) id) := by
  exact (p3QuadraticLaurentResidueLinearMap_eq_dual_coordinates K
    ((p3NegativeTwistCechTermToLaurent K 6 3 w.1) id)).symm

/-- Evaluating the full native dual at any quadratic is the literal
Laurent coefficient of the product; this is not limited to basis monomials. -/
theorem p3NegativeSix_raw_residue_dual_apply_quadratic
    (w : P3RawTopCocycle K 6) (q : homogeneousSubmodule (Fin 4) K 2) :
    (p3QuadraticDualCoordinateEquiv K).symm (p3NegativeSixTopResidueCoordinates K w) q =
      (polynomialToLaurent (K := K) (q : MvPolynomial (Fin 4) K) *
        ((p3NegativeTwistCechTermToLaurent K 6 3 w.1) id)).coeff (p3SerreDualExponent 0) := by
  rw [p3NegativeSix_raw_residue_dual_eq_multiplication]
  rfl

end PfaffianDescent.ProjectiveNegativeTwist
