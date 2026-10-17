import PfaffianDescent.VoisinGenericSixteenFixedCurveCanonicalIdealChart
import PfaffianDescent.VoisinGenericSixteenIdealChartCubicRank

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Any fixed curve containing the actual generic sixteen-point scheme has
at most four independent homogeneous cubic ideal equations. -/
theorem cubicSixteenFixedCurve_cubicIdealPiece_finrank_le_four
    {K : Type u} [Field K]
    {m : ℕ}
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 16).toScheme.functionField))
    (e : Fin m ≃ Monomials (Fin 4) 3)
    (frame : Fin 16 → homogeneousSubmodule (Fin 4) K 3)
    (hframe : LinearIndependent K frame)
    (hno : HomogeneousSixteenNoCommonResidueFieldEquationAt cubic hcubic e frame hframe z)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 16 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 16 a ha).val.subschemeι) :
    let Q := cubicConfigurationBase cubic hcubic 16
    finrank Q.functionField (homogeneousIdealPiece C 3) ≤ 4 := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  obtain ⟨T⟩ := exists_cubicSixteenFixedCurve_canonicalIdealChart
    cubic hcubic a ha C hCp h hfac
  exact cubicSixteenOrderedLift_idealChart_cubicIdealPiece_finrank_le_four
    cubic hcubic a ha z hz e frame hframe hno C hCp T

/-- The four-cubic bound with its ordered-lift witness selected internally. -/
theorem cubicConfigurationGenericSixteen_fixedCurve_cubicIdealPiece_finrank_le_four
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
    {m : ℕ} (e : Fin m ≃ Monomials (Fin 4) 3)
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4)
      (cubicConfigurationBase cubic hcubic 16).functionField))
    (hCp : cubic.map a.hom ∈ C.toIdeal)
    (h : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 16 a ha).val.subscheme ⟶ scheme C)
    (hfac : h ≫ homogeneousFixedCurveToCubic
        (cubic.map a.hom) (hcubic.map a.hom) C hCp =
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 16 a ha).val.subschemeι) :
    let Q := cubicConfigurationBase cubic hcubic 16
    finrank Q.functionField (homogeneousIdealPiece C 3) ≤ 4 := by
  dsimp only
  have hgeneric :
      let O := (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 16).left
      let Q₀ := (projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme
      let π := projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16
      let η := Q₀.fromSpecStalk (genericPoint Q₀)
        (IsLocalRing.closedPoint Q₀.functionField)
      ∃ (frame : Fin 16 → homogeneousSubmodule (Fin 4) K 3)
        (hframe : LinearIndependent K frame) (z : O),
        π z = η ∧
        HomogeneousSixteenNoCommonResidueFieldEquationAt
          cubic hcubic e frame hframe z := by
    exact exists_orderedPointOver_genericSixteen_with_noCommonCubicEquation
      cubic hcubic hcubic_ne hcubic_prime e
  obtain ⟨frame, hframe, z, hz, hno⟩ := hgeneric
  exact cubicSixteenFixedCurve_cubicIdealPiece_finrank_le_four
    cubic hcubic a ha z hz e frame hframe hno C hCp h hfac

end PfaffianDescent
