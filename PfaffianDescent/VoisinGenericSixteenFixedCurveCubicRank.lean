import PfaffianDescent.VoisinGenericSixteenFixedCurveCanonicalChart
import PfaffianDescent.VoisinGenericSixteenEquationChartRank

/-!
# Cubic rank on the normalized chart of a fixed curve
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Every fixed-curve factorization of the actual generic sixteen-point
scheme has a normalized chart on which the cubic vanishing system modulo the
surface equation has dimension exactly three. -/
theorem exists_cubicSixteenFixedCurve_chart_cubicVanishingModuloEquation_finrank_three
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
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    ∃ (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (hpx : (cubic.map a.hom).eval₂
        (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 0),
      cubicVanishingSectionsModuloEquationFinrank
        (cubic.map a.hom) (hcubic.map a.hom) x hpx = 3 := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  exact exists_cubicSixteenOrderedLift_equationChart_cubicRank_three
    cubic hcubic a ha z hz e frame hframe hno
    (exists_cubicSixteenFixedCurve_canonicalNormalizedChart
      cubic hcubic a ha C hCp h hfac)

end PfaffianDescent
