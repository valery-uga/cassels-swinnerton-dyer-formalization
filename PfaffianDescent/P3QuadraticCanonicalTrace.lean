import PfaffianDescent.TwistCechLaurentMultiplication
import PfaffianDescent.P3RawLaurentPolynomialEvaluation
import PfaffianDescent.P3CanonicalCohomologyTrace

/-! # Quadratic pairing as the canonical scalar trace of actual multiplication -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry MvPolynomial
namespace PfaffianDescent.ProjectiveNegativeTwist
open LaurentLocalization LaurentCechExact
universe u
variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => MvPolynomial.homogeneousSubmodule (Fin 4) K

/-- Actual sheaf multiplication induces a map of raw top cocycles. -/
def p3RawTopCocycleMultiply (m d : ℕ) (q : PS d)
    (w : P3RawTopCocycle K (m + d)) : P3RawTopCocycle K m :=
  ⟨(p3NegativeTwistCechMultiplication K m d q).f 3 w.1, by
    change (p3NegativeTwistCechComplex (K := K) m).d 3 4
      ((p3NegativeTwistCechMultiplication K m d q).f 3 w.1) = 0
    have h := CategoryTheory.congr_fun
      ((p3NegativeTwistCechMultiplication K m d q).comm 3 4) w.1
    have hw : (p3NegativeTwistCechComplex (K := K) (m + d)).d 3 4 w.1 = 0 := w.2
    simpa only [ConcreteCategory.comp_apply, hw, map_zero] using h⟩

/-- The native quadratic dual evaluated at any quadratic equals the
canonical scalar trace of ACTUAL multiplication of its representative. -/
theorem p3NegativeSix_raw_quadratic_pairing_eq_canonical_trace
    (w : P3RawTopCocycle K 6) (q : PS 2) :
    (p3QuadraticDualCoordinateEquiv K).symm (p3NegativeSixTopResidueCoordinates K w) q =
      p3NegativeFourTopTrace K (p3RawTopCocycleMultiply K 4 2 q w) := by
  rw [p3NegativeSix_raw_residue_dual_apply_quadratic]
  change _ =
    (p3NegativeTwistCechTermToLaurent K 4 3
      ((p3NegativeTwistCechMultiplication K 4 2 q).f 3 w.1) id).coeff
        (p3SerreDualExponent 0)
  rw [p3NegativeTwistCechMultiplication_toLaurent]

/-- The same equality uses the actual augmented Ext trace, rather than
an abstract residue-coordinate functional. -/
theorem p3NegativeSix_raw_quadratic_pairing_eq_augmented_trace
    [HasExt.{u} (Proj PS).Modules]
    (w : P3RawTopCocycle K 6) (q : PS 2) :
    (p3QuadraticDualCoordinateEquiv K).symm (p3NegativeSixTopResidueCoordinates K w) q =
      p3NegativeFourAugmentedExtTraceEquiv K
        (p3RawTopCocycleToAugmentedExt K 4 (p3RawTopCocycleMultiply K 4 2 q w)) := by
  rw [p3NegativeFourAugmentedExtTraceEquiv_raw]
  exact p3NegativeSix_raw_quadratic_pairing_eq_canonical_trace K w q

end PfaffianDescent.ProjectiveNegativeTwist
