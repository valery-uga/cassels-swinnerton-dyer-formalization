import PfaffianDescent.VoisinGenericDegreeEightFixedCurveDichotomy
import PfaffianDescent.NormalizedChartAlgebraTransport

/-!
# The normalized fixed-curve chart in its source coefficient algebra
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A factorization of the generic sixteen-point scheme through a fixed
curve supplies a normalized ambient chart in the algebra induced by that
factorization. -/
theorem exists_cubicSixteenFixedCurve_sourceNormalizedChart
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
    letI : IsFinite (h ≫ toBase C) :=
      (fixedCurve_factor_toBase (cubic.map a.hom) (hcubic.map a.hom)
        C hCp D.val.subschemeι h hfac).symm ▸ D.property.1
    letI sourceAlgebra := finiteSchemeCoefficientAlgebra (h ≫ toBase C)
    Nonempty (@NormalizedAmbientEquationChart Q.functionField
        Γ(D.val.subscheme, ⊤) _ _ sourceAlgebra (Fin 4) _
        (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) Q.functionField))
        (D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
          hypersurfaceToAmbient (cubic.map a.hom) (hcubic.map a.hom))
        (cubic.map a.hom)) := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 16
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 16 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 16 a ha
  letI : IsFinite pD := D.property.1
  letI : IsFinite
      (D.val.subschemeι ≫ hypersurfaceToBase
        (cubic.map a.hom) (hcubic.map a.hom)) := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  have hfactorBase : h ≫ toBase C = pD :=
    fixedCurve_factor_toBase (cubic.map a.hom) (hcubic.map a.hom)
      C hCp D.val.subschemeι h hfac
  letI : IsFinite (h ≫ toBase C) := hfactorBase.symm ▸ inferInstance
  letI sourceAlgebra := finiteSchemeCoefficientAlgebra (h ≫ toBase C)
  obtain ⟨ell, hell, x, he, hellOne, -, hxC, hpoint⟩ :=
    fixedCurve_factor_normalized_ambient_chart
      (cubic.map a.hom) (hcubic.map a.hom) C hCp
      D.val.subschemeι h hfac
  exact ⟨{
    chart := {
      ell := ell
      hell := hell
      x := x
      he := he
      hellOne := hellOne
      hpoint := hpoint }
    equationZero := hxC (cubic.map a.hom) hCp }⟩

end PfaffianDescent
