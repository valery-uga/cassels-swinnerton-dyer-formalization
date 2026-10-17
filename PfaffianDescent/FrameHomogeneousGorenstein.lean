import PfaffianDescent.FrameParameterFrobenius
import PfaffianDescent.FrobeniusInjectiveDimension
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

namespace PfaffianDescent.FrameCoordinateRing
open CategoryTheory Polynomial
section
variable {K : Type*} [Field K] [CharZero K]

/-- The actual homogeneous coordinate ring of the five-point projective frame
has a self-injective resolution of length at most one. -/
theorem self_injectiveDimensionLE_one :
    HasInjectiveDimensionLE (ModuleCat.of (FrameCoordinateRing K) (FrameCoordinateRing K)) 1 :=
  frobenius_self_injectiveDimensionLE_one (F := FractionRing K[X]) parameterFunctional
    (ringMultiplicationDual_bijective parameterBasis parameterFunctional
      parameter_multiplicationGram_isUnit)

/-- The homogeneous coordinate ring is Noetherian with finite self-injective
dimension, the homological Gorenstein criterion. -/
theorem homogeneous_ring_gorenstein :
    IsNoetherianRing (FrameCoordinateRing K) ∧
      HasInjectiveDimensionLE (ModuleCat.of (FrameCoordinateRing K) (FrameCoordinateRing K)) 1 :=
  ⟨inferInstance, self_injectiveDimensionLE_one⟩

end
end PfaffianDescent.FrameCoordinateRing
