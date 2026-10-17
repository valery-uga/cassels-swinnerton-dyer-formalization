import PfaffianDescent.VoisinGenericSixteenFixedCurveSourceIdealChart

/-!
# Transporting the fixed-curve chart to the canonical coefficient algebra
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The fixed-curve normalized chart, including its surface equation, can be
read in the canonical coefficient algebra of the generic sixteen-point scheme. -/
theorem exists_cubicSixteenFixedCurve_canonicalIdealChart
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 16)]
    [Infinite (cubicConfigurationBase cubic hcubic 16).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 16).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap cubic hcubic 16 ≫
      cubicConfigurationToBase cubic hcubic 16)
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
    letI canonicalAlgebra := finiteSchemeCoefficientAlgebra pD
    Nonempty (@NormalizedAmbientIdealChart Q.functionField
        Γ(D.val.subscheme, ⊤) _ _ canonicalAlgebra (Fin 4) _
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q.functionField))
        (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
          hypersurfaceToAmbient (cubic.map a.hom) (hcubic.map a.hom))
        C) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  letI : IsFinite pD := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  have hfactorBase : h ≫ toBase C = pD :=
    fixedCurve_factor_toBase (cubic.map a.hom) (hcubic.map a.hom)
      C hCp D.val.subschemeι h hfac
  letI : IsFinite (h ≫ toBase C) := hfactorBase.symm ▸ inferInstance
  letI sourceAlgebra := finiteSchemeCoefficientAlgebra (h ≫ toBase C)
  obtain ⟨T⟩ := exists_cubicSixteenFixedCurve_sourceIdealChart
    cubic hcubic a ha C hCp h hfac
  let canonicalAlgebra := finiteSchemeCoefficientAlgebra pD
  have hAlg : sourceAlgebra = canonicalAlgebra := by
    dsimp only [sourceAlgebra, canonicalAlgebra]
    simpa only [hfactorBase]
  exact ⟨NormalizedAmbientIdealChart.transport
    sourceAlgebra canonicalAlgebra hAlg
    (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 4) Q.functionField))
    (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
      hypersurfaceToAmbient (cubic.map a.hom) (hcubic.map a.hom))
    C T⟩

end PfaffianDescent
