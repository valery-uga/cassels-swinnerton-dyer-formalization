import PfaffianDescent.CubicElevenPointGroundSerreRankData

/-! Upgrade the SAME actual canonical Serre evaluation to its native
principal configuration rank chart. -/
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

abbrev cubicElevenPointGroundSerreRank_of_actual_evaluation
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left]
    [IsIntegral (cubicConfigurationBase p hp 11)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 11).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 11 ≫
      cubicConfigurationToBase p hp 11)
    (hEval : CubicElevenPointGroundSerreEvaluationFor p hp a ha) := by
  let F := (cubicConfigurationBase p hp 11).functionField
  let P := p.map a.hom
  let hP := hp.map a.hom
  letI : CharZero F := charZero_of_injective_ringHom a.hom.injective
  letI : Smooth (hypersurfaceToBase P hP) := smooth_hypersurfaceToBase_map a.hom p hp
  have hP0 : P ≠ 0 := cubicConfigurationCoefficientChange_ne_zero p hp 11 a hp0
  let D := cubicConfigurationGenericFiniteSubscheme p hp 11 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 11 a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  let L := Γ(D.val.subscheme, ⊤)
  letI : Field L :=
    (cubicConfigurationGenericFiniteSubscheme_isField p hp 11 a ha (0 : Fin 11)).toField
  let i := finiteSubschemeDatumSpecMap (hypersurfaceToBase P hP) D
  exact cubicFieldChartSerreRankData_of_actual_evaluation P hP hP0 i hEval

end PfaffianDescent
