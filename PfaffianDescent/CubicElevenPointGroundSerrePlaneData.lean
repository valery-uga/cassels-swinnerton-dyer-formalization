import PfaffianDescent.CubicFieldChartSerrePlaneFactory
import PfaffianDescent.CubicElevenPointGroundSerreEvaluationFactory

/-! Actual native Serre rank chart on the SAME canonical degree-eleven
subscheme over its actual unordered function field. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

local instance {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hO : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left] :
    IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 11).left := hO

def CubicElevenPointGroundSerrePlaneFor
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left]
    [IsIntegral (cubicConfigurationBase p hp 11)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 11).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 11 ≫
      cubicConfigurationToBase p hp 11) : Prop :=
    let P := p.map a.hom
    let hP := hp.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme p hp 11 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap p hp 11 a ha
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Field Γ(D.val.subscheme, ⊤) :=
      (cubicConfigurationGenericFiniteSubscheme_isField p hp 11 a ha (0 : Fin 11)).toField
    CubicFieldChartSerrePlaneData P hP
      (finiteSubschemeDatumSpecMap (hypersurfaceToBase P hP) D)

end PfaffianDescent
