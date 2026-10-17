import AllCharacteristics.ProjectiveFiniteEtaleConfiguration
import AllCharacteristics.HomogeneousTupleGenericSpecialization
import AllCharacteristics.ProjectiveConfigurationRegularity
import AllCharacteristics.ProjectiveConfigurationIntegrality

/-!
# Specializing a generic tuple from a finite étale configuration

An actual finite étale rank-`n` subscheme supplies the rational point of the
configuration movement base.  Consequently, once the generic geometric
argument supplies a rank-`m` tuple over that base's function field, it
specializes to an effective degree-`m` cycle over the original field.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AllCharacteristics
namespace HomogeneousProjective

universe u

variable {K : Type u} [Field K] [CharZero K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra
variable (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))

/-- A generic effective rank-`m` tuple over the rank-`n` unordered
configuration space specializes at any actual finite étale rank-`n`
subscheme.  Thus the only geometric input left to a Voisin application is
the displayed function-field tuple and its base equation. -/
theorem effectiveZeroCycle_of_finiteEtaleSubscheme_configurationFunctionFieldTuple
    (n m : ℕ) [IsSeparated (toBase I)] [Smooth (toBase I)]
    [IsIntegral (orderedFamilyConfigurationOver (toBase I) n).left]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading I) (toBase I) n).toScheme]
    (D : FiniteSubschemeDatum (toBase I) n)
    [Etale (D.val.subschemeι ≫ toBase I)]
    (s : Spec (projectiveConfigurationQuotientOpen
        (grading I) (toBase I) n).toScheme.functionField ⟶ tupleQuotient I m)
    (hs : s ≫ tupleQuotientToBase I m =
      (projectiveConfigurationQuotientOpen
          (grading I) (toBase I) n).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading I) (toBase I) n).toScheme) ≫
        projectiveConfigurationQuotientToBase (grading I) (toBase I) n) :
    ∃ z : EffectiveZeroCycle (scheme I),
      EffectiveZeroCycle.degree (toBase I) z = m := by
  have hsep : IsSeparated (toBase I) := inferInstance
  have hsmooth : Smooth (toBase I) := inferInstance
  have het : Etale (D.val.subschemeι ≫ toBase I) := inferInstance
  letI : IsSeparated (toBase I) := hsep
  let f' : Proj (grading I) ⟶ Spec (.of K) := toBase I
  letI : IsSeparated f' := hsep
  letI : Smooth f' := hsmooth
  let D' : FiniteSubschemeDatum f' n := D
  letI : Etale (D'.val.subschemeι ≫ f') := by
    dsimp only [D', f']
    exact het
  obtain ⟨c, hc⟩ :=
    exists_projectiveConfigurationPoint_of_finiteEtaleSubscheme
      (𝒜 := grading I) (K := K) f' n (D := D')
  let B := (projectiveConfigurationQuotientOpen
    (grading I) (toBase I) n).toScheme
  let b := projectiveConfigurationQuotientToBase (grading I) (toBase I) n
  haveI : IsIntegral B := inferInstance
  haveI : IsRegularLocalRing
      (B.presheaf.stalk (c (IsLocalRing.closedPoint K))) :=
    isRegularLocalRing_projectiveConfigurationQuotient_stalk
      (grading I) f' n
      (fun y ↦ isRegularLocalRing_spec_stalk K y)
      (c (IsLocalRing.closedPoint K))
  exact effectiveZeroCycle_of_parameter_functionField_tuple
    I m b c hc s hs

end HomogeneousProjective
end AllCharacteristics
