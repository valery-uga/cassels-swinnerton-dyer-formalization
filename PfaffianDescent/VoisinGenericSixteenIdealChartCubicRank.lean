import PfaffianDescent.VoisinGenericSixteenNormalizedChartRank
import PfaffianDescent.VoisinFixedCurveCubicIdealRank

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- On any normalized chart of the actual generic sixteen-point scheme, a
curve containing the scheme has at most four cubic ideal equations. -/
theorem cubicSixteenOrderedLift_idealChart_cubicIdealPiece_finrank_le_four
    {K : Type u} [Field K]
    {m : ℕ}
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 16).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
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
    (hno : HomogeneousSixteenNoCommonResidueFieldEquationAt cubic hcubic e frame hframe z) :
    let Q := cubicConfigurationBase cubic hcubic 16
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 16).left
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
    let b := cubicSixteenOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    let φ : Fin 16 → Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z :=
      fun i => cubicSixteenOrderedLiftCoefficientChangedComponentAlgHom
        cubic hcubic a ha z hz i
    ∀ (C : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) Q.functionField))
      (hCp : p' ∈ C.toIdeal)
      (T : @NormalizedAmbientIdealChart Q.functionField
        Γ(D.val.subscheme, ⊤) _ _ (finiteSchemeCoefficientAlgebra pD)
        (Fin 4) _
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q.functionField))
        (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
          hypersurfaceToAmbient p' hp') C),
      finrank Q.functionField (homogeneousIdealPiece C 3) ≤ 4 := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  haveI : Module.Finite Q.functionField Γ(D.val.subscheme, ⊤) :=
    finiteSchemeCoefficient_finite pD
  intro C hCp T
  have hpx : (cubic.map a.hom).eval₂
      (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) T.chart.x = 0 :=
    T.idealZero (cubic.map a.hom) hCp
  have hrank :=
    cubicSixteenOrderedLift_packagedAmbientChart_cubicVanishingModuloEquation_finrank_three
      cubic hcubic a ha z hz e frame hframe hno T.chart hpx
  exact fixedCurveCubicIdealPiece_finrank_le_four_of_cubicRank_three
    (cubic.map a.hom) (hcubic.map a.hom) C
    T.chart.x hpx T.idealZero hrank

end PfaffianDescent
