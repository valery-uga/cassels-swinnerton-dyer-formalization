import AllCharacteristics.ProjectiveConfigurationClosedPointIntegrality
import AllCharacteristics.ProjectiveConfigurationGenericSpecialization

/-!
# Specialization from a closed point and a rational configuration section

This packages the generic-point specialization step in the form needed for
the degree-ten argument: a characteristic-zero closed point gives the
integrality and a rational point of the configuration quotient, while a
rational section supplies the generic function-field point.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AllCharacteristics

universe u v
variable {A : Type u} [CommRing A] {sigma : Type v} [SetLike sigma A]
  [AddSubgroupClass sigma A]
variable (graded : ℕ → sigma) [GradedRing graded]

/-- A rational section over the unordered degree-`n` configuration quotient
specializes to a point of a proper geometrically integral smooth family as
soon as that family has a degree-`n` closed point. -/
theorem proper_point_of_projectiveConfiguration_rationalMap_of_closedPoint
    {K : Type u} [Field K] [CharZero K]
    (g : Proj graded ⟶ Spec (.of K)) [IsProper g] [Smooth g] [GeometricallyIntegral g]
    (x : closedPoints (Proj graded)) (n : ℕ)
    (hx : g.residueDegree x.1 = n)
    (s : (projectiveConfigurationQuotientOpen graded g n).toScheme.RationalMap (Proj graded))
    (hs : s.compHom g = (projectiveConfigurationQuotientToBase graded g n).toRationalMap) :
    ∃ q : Spec (.of K) ⟶ Proj graded, q ≫ g = 𝟙 _ := by
  let B := (projectiveConfigurationQuotientOpen graded g n).toScheme
  let b := projectiveConfigurationQuotientToBase graded g n
  let _ : IsIntegral B :=
    isIntegral_projectiveConfigurationQuotientOpen_of_closedPoint graded g x n hx
  obtain ⟨c, hc⟩ := exists_projectiveConfigurationPoint_of_closedPoint graded g x n hx
  apply proper_point_of_projectiveConfiguration_functionField_point graded g n c hc
    s.fromFunctionField
  have hcomp : (s.compHom g).fromFunctionField = s.fromFunctionField ≫ g := by
    obtain ⟨s, rfl⟩ := s.exists_rep
    rfl
  calc
    s.fromFunctionField ≫ g = (s.compHom g).fromFunctionField := hcomp.symm
    _ = b.toRationalMap.fromFunctionField := congrArg (fun r ↦ r.fromFunctionField) hs
    _ = B.fromSpecStalk (genericPoint B) ≫ b := by
      simp [B, b]

end AllCharacteristics
