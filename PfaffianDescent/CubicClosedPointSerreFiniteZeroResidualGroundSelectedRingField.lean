import Mathlib.Algebra.Field.IsField
noncomputable section
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
/-- Derive a field while preserving the actual given commutative ring verbatim. -/
@[instance_reducible]
def cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField
    {R : Type u} [CommRing R] (h : IsField R) : Field R :=
  { h.toField with toCommRing := ‹CommRing R› }

theorem cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField_toCommRing
    {R : Type u} [CommRing R] (h : IsField R) :
    (cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField h).toCommRing =
      ‹CommRing R› := rfl

theorem cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField_eq
    {R : Type u} [CommRing R] (h : IsField R) :
    cubicClosedPointSerreFiniteZeroResidual_groundSelectedIsFieldField h = h.toField := rfl
end PfaffianDescent.ProjectiveNegativeTwist
