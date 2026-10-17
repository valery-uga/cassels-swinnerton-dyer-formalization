import PfaffianDescent.VoisinGenericCubicSixteenEvaluation
import PfaffianDescent.CubicSurfaceSectionDimensions

/-!
# No low-degree equation through the generic sixteen points

The entire space of linear or quadratic equations has dimension at most
sixteen. Applying fixed-frame incidence to that full space therefore excludes
even a low-degree equation whose coefficients are chosen after passing to the
generic configuration field. This avoids the fixed-frame versus varying-frame
quantifier problem in these two degrees.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.UniversalHomogeneous
open HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- At an ordered lift of the generic sixteen-point configuration, no
nonzero linear or quadratic equation over the residue field vanishes at all
sixteen marked points. The frame is the entire homogeneous space, so this
also covers equations varying with the configuration. -/
theorem exists_orderedPointOver_genericSixteen_with_noCommonLowDegreeEquation
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime :
      (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m : ℕ} (hd : 0 < d) (hd3 : d < 3)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme] :
    let W := homogeneousSubmodule (Fin 4) K d
    let frame := Module.finBasis K W
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let Q := (projectiveConfigurationQuotientOpen
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 16).toScheme
    let π := projectiveConfigurationQuotientMap
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 16
    let η := Q.fromSpecStalk (genericPoint Q)
      (IsLocalRing.closedPoint Q.functionField)
    ∃ z : O, π z = η ∧
      HomogeneousSixteenNoCommonResidueFieldEquationAt
        cubic hcubic e frame frame.linearIndependent z := by
  dsimp only
  let W := homogeneousSubmodule (Fin 4) K d
  let frame := Module.finBasis K W
  have hdim : Module.finrank K W ≤ 16 := by
    rw [show Module.finrank K W = (d + 3).choose 3 from
      four_variable_homogeneous_finrank (K := K) d]
    interval_cases d <;> decide
  have hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0 := by
    intro z hz hmem
    let v : W := ⟨z, hz⟩
    have hv : cubicSurfaceProjection cubic hcubic d v = 0 := by
      change Ideal.Quotient.mk (equationIdeal cubic hcubic).toIdeal z = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hvzero : v = 0 :=
      (cubicSurfaceProjection_injective_of_lt_three
        cubic hcubic hcubic_ne d hd3) (by simpa using hv)
    exact congrArg Subtype.val hvzero
  exact exists_orderedPointOver_genericSixteen_with_noCommonFrameEquation
    cubic hcubic hcubic_ne hcubic_prime hd W
      (fun z hz => hz) hseparate hdim
      frame frame (fun _ => rfl) frame.linearIndependent
      frame.linearIndependent rfl e

end PfaffianDescent
