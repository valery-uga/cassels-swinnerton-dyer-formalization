import AllCharacteristics.HomogeneousTupleResidueCycle
import AllCharacteristics.ProjectiveTupleQuotientFinitePresentation
import AllCharacteristics.ProperFamilyGenericPointSpecialization

/-!
# Specializing generic effective tuples

This is the specialization bridge needed in Voisin's moving argument.  A
generic residual effective tuple gives a point of the full unordered-tuple
quotient over the function field of a regular parameter scheme.  Universal
closedness of the quotient then specializes that point at the original
field-valued parameter, including when points collide in the special fiber.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AllCharacteristics
namespace HomogeneousProjective
universe u

variable {K : Type u} [Field K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) (n : ℕ)

/-- A function-field point of the full unordered-tuple quotient specializes
at every regular field-valued point of an integral parameter scheme.  The
special point remains in the full quotient, so collisions are allowed. -/
theorem tupleQuotient_point_of_parameter_functionField_point
    {B : Scheme.{u}} [IsIntegral B]
    (b : B ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ B) (hc : c ≫ b = 𝟙 _)
    [IsRegularLocalRing
      (B.presheaf.stalk (c (IsLocalRing.closedPoint K)))]
    (s : Spec B.functionField ⟶ tupleQuotient I n)
    (hs : s ≫ tupleQuotientToBase I n =
      B.fromSpecStalk (genericPoint B) ≫ b) :
    ∃ q : Spec (.of K) ⟶ tupleQuotient I n,
      q ≫ tupleQuotientToBase I n = 𝟙 _ := by
  letI : LocallyOfFinitePresentation (tupleQuotientToBase I n) :=
    @locallyOfFinitePresentation_projectiveOrderedTupleQuotientToBase
      _ _ _ _ _ (grading I) _ _ _ _ (toBase I)
        ((isProper_toBase (σ := σ) I).toLocallyOfFiniteType) n
  exact universallyClosed_point_of_parameter_functionField_point
    b (tupleQuotientToBase I n) c hc s hs

/-- A generic unordered effective tuple over the function field of a regular
parameter scheme specializes to an effective zero-cycle of the same degree on
the original projective scheme.  Repeated points in the special tuple are
retained as cycle multiplicities. -/
theorem effectiveZeroCycle_of_parameter_functionField_tuple
    [CharZero K]
    {B : Scheme.{u}} [IsIntegral B]
    (b : B ⟶ Spec (.of K))
    (c : Spec (.of K) ⟶ B) (hc : c ≫ b = 𝟙 _)
    [IsRegularLocalRing
      (B.presheaf.stalk (c (IsLocalRing.closedPoint K)))]
    (s : Spec B.functionField ⟶ tupleQuotient I n)
    (hs : s ≫ tupleQuotientToBase I n =
      B.fromSpecStalk (genericPoint B) ≫ b) :
    ∃ z : EffectiveZeroCycle (scheme I),
      EffectiveZeroCycle.degree (toBase I) z = n := by
  obtain ⟨q, hq⟩ :=
    tupleQuotient_point_of_parameter_functionField_point I n b c hc s hs
  exact tupleQuotient_exists_effectiveZeroCycle I n q hq

end HomogeneousProjective
end AllCharacteristics
