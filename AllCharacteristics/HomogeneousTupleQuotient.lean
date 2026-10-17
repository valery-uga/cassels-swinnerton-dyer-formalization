import AllCharacteristics.ProjectiveOrderedTupleQuotient
import AllCharacteristics.HomogeneousProjective

/-!
# Actual unordered-tuple quotients for homogeneous projective equations

The quotient construction is applied to the actual Proj of a homogeneous
polynomial quotient. In finitely many variables its quotient morphism from
the entire ordered relative power is finite, proper, and surjective over
any commutative coefficient ring.
-/

open AlgebraicGeometry CategoryTheory
namespace AllCharacteristics
namespace HomogeneousProjective
universe u
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ R)) (n : ℕ)

/-- The actual unordered-tuple quotient scheme of a homogeneous projective scheme. -/
noncomputable def tupleQuotient : Scheme.{u} :=
  projectiveOrderedTupleQuotient (grading I) (toBase I) n

/-- The actual quotient map from the entire ordered relative power of the homogeneous scheme. -/
noncomputable def tupleQuotientMap : (orderedFamilyPowerOver (toBase I) n).left ⟶ tupleQuotient I n :=
  projectiveOrderedTupleQuotientMap (grading I) (toBase I) n

/-- The constructed unordered-tuple quotient retains the original coefficient base. -/
noncomputable def tupleQuotientToBase : tupleQuotient I n ⟶ Spec (.of R) :=
  projectiveOrderedTupleQuotientToBase (grading I) (toBase I) n

/-- The quotient map factors the actual original coefficient morphism. -/
theorem tupleQuotientMap_toBase :
    tupleQuotientMap I n ≫ tupleQuotientToBase I n = (orderedFamilyPowerOver (toBase I) n).hom :=
  projectiveOrderedTupleQuotientMap_toBase (grading I) (toBase I) n

/-- The full unordered-tuple quotient of a homogeneous projective scheme is
universally closed over the coefficient ring.  This is the valuative
existence property used to specialize points representing effective cycles. -/
instance universallyClosed_tupleQuotientToBase [Finite σ] :
    UniversallyClosed (tupleQuotientToBase I n) := by
  exact @universallyClosed_projectiveOrderedTupleQuotientToBase
    _ _ _ _ _ (grading I) _ _ _ (toBase I) n (isProper_toBase (σ := σ) I)

/-- The constructed full quotient map is integral over every coefficient ring. -/
instance isIntegralHom_tupleQuotientMap : IsIntegralHom (tupleQuotientMap I n) :=
  isIntegralHom_projectiveOrderedTupleQuotientMap (grading I) (toBase I) n

/-- The constructed full quotient map is surjective over every coefficient ring. -/
instance surjective_tupleQuotientMap : Surjective (tupleQuotientMap I n) :=
  surjective_projectiveOrderedTupleQuotientMap (grading I) (toBase I) n

/-- In finitely many variables the constructed full quotient map is finite. -/
instance isFinite_tupleQuotientMap [Finite σ] : IsFinite (tupleQuotientMap I n) := by
  let f : Proj (grading I) ⟶ Spec (.of R) := toBase I
  have : IsProper f := isProper_toBase I
  exact isFinite_projectiveOrderedTupleQuotientMap (grading I) f n

/-- In finitely many variables the constructed full quotient map is proper. -/
instance isProper_tupleQuotientMap [Finite σ] : IsProper (tupleQuotientMap I n) := by
  infer_instance

end HomogeneousProjective
end AllCharacteristics
