import AllCharacteristics.ProjectiveConfigurationGenericSpecialization
import AllCharacteristics.UniversalProjectiveIncidenceProper

/-!
# Generic avoidance for universal projective incidence

After pulling the universal hypersurface incidence back to an integral
parameter scheme, a proper incidence image is a closed bad locus.  Its generic
function-field point therefore avoids that locus.  This packages the passage
from universal projective equations to the generic-point argument used in
Voisin's construction.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

namespace AllCharacteristics
namespace UniversalHomogeneous

open HomogeneousProjective

universe u

variable (R : Type u) [CommRing R] (σ : Type) [Finite σ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- If a parameter map has a proper universal-incidence image, then its
generic function-field point is not represented by a pair consisting of an
ambient point and an equation vanishing at that point. -/
theorem genericFunctionField_closedPoint_avoids_projectiveUniversalIncidence
    {B : Scheme.{u}} [IsIntegral B]
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d)
    (hproper :
      Set.range (projectiveUniversalIncidenceBaseChangeToBase R σ d b) ≠ Set.univ) :
    B.fromSpecStalk (genericPoint B) (IsLocalRing.closedPoint B.functionField) ∉
      Set.range (projectiveUniversalIncidenceBaseChangeToBase R σ d b) :=
  genericFunctionField_closedPoint_avoids_proper_closed B
    (isClosed_range_projectiveUniversalIncidenceBaseChangeToBase R σ d b) hproper

/-- In its intrinsic form, generic avoidance says that the generic parameter
does not map into the universal incidence locus. -/
theorem genericFunctionField_closedPoint_avoids_projectiveUniversalIncidence_preimage
    {B : Scheme.{u}} [IsIntegral B]
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d)
    (hproper : b ⁻¹' Set.range (projectiveUniversalIncidence R σ d) ≠ Set.univ) :
    B.fromSpecStalk (genericPoint B) (IsLocalRing.closedPoint B.functionField) ∉
      b ⁻¹' Set.range (projectiveUniversalIncidence R σ d) := by
  have hproper' :
      Set.range (projectiveUniversalIncidenceBaseChangeToBase R σ d b) ≠ Set.univ := by
    rwa [range_projectiveUniversalIncidenceBaseChangeToBase R σ d b]
  rw [← range_projectiveUniversalIncidenceBaseChangeToBase R σ d b]
  exact genericFunctionField_closedPoint_avoids_projectiveUniversalIncidence R σ d b hproper'

/-- The generic point of an integral target avoids the bad locus defined by a
universal equation on any proper ambient parameter space, provided that this
closed locus is not the whole target. -/
theorem genericFunctionField_closedPoint_avoids_projectiveUniversalIncidenceToTarget
    {B C : Scheme.{u}} [IsIntegral C]
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d)
    (π : B ⟶ C) [IsProper π]
    (hproper : Set.range
      (projectiveUniversalIncidenceBaseChangeToTarget R σ d b π) ≠ Set.univ) :
    C.fromSpecStalk (genericPoint C) (IsLocalRing.closedPoint C.functionField) ∉
      Set.range (projectiveUniversalIncidenceBaseChangeToTarget R σ d b π) :=
  genericFunctionField_closedPoint_avoids_proper_closed C
    (isClosed_range_projectiveUniversalIncidenceBaseChangeToTarget R σ d b π) hproper

/-- A proper ambient parameter space defines a proper universal-vanishing
bad locus on an integral target; a proper such locus misses its generic
function-field point. -/
theorem genericFunctionField_closedPoint_avoids_projectiveUniversalIncidence_image
    {B C : Scheme.{u}} [IsIntegral C]
    (b : B ⟶ Proj (MvPolynomial.homogeneousSubmodule σ R) ⨯
      projectiveParameters R σ d)
    (π : B ⟶ C) [IsProper π]
    (hproper : π '' (b ⁻¹' Set.range (projectiveUniversalIncidence R σ d)) ≠ Set.univ) :
    C.fromSpecStalk (genericPoint C) (IsLocalRing.closedPoint C.functionField) ∉
      π '' (b ⁻¹' Set.range (projectiveUniversalIncidence R σ d)) := by
  have hproper' : Set.range
      (projectiveUniversalIncidenceBaseChangeToTarget R σ d b π) ≠ Set.univ := by
    rwa [range_projectiveUniversalIncidenceBaseChangeToTarget R σ d b π]
  rw [← range_projectiveUniversalIncidenceBaseChangeToTarget R σ d b π]
  exact genericFunctionField_closedPoint_avoids_projectiveUniversalIncidenceToTarget
    R σ d b π hproper'

end UniversalHomogeneous
end AllCharacteristics
