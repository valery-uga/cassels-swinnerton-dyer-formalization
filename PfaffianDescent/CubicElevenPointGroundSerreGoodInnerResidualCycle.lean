import PfaffianDescent.CubicElevenPointGroundSerreGoodFactory
import PfaffianDescent.CubicFieldChartSerreGoodGenericThreeCycle
import PfaffianDescent.CubicFieldPointChartClosedImmersion
import PfaffianDescent.CubicGenericThreeEffectiveEightType

/-! The actual generic-eleven factory's chosen chart and Serre bundle produce
a degree-eight cycle over the actual inner generic-three function field. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicElevenPointGroundSerreGood_innerGenericThree_effectiveEight
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left]
    [IsIntegral (cubicConfigurationBase p hp 11)]
    (a₁₁ : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 11).functionField)
    (ha₁₁ : Spec.map a₁₁ = cubicConfigurationGenericBaseMap p hp 11 ≫
      cubicConfigurationToBase p hp 11)
    (hGood : CubicElevenPointGroundSerreGoodFor p hp a₁₁ ha₁₁) :
    CubicGenericThreeEffectiveEightType (p.map a₁₁.hom) (hp.map a₁₁.hom) := by
  letI : IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 11).left := by
    change IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left
    infer_instance
  let F := (cubicConfigurationBase p hp 11).functionField
  letI : Algebra K F := a₁₁.hom.toAlgebra
  letI : CharZero F := charZero_cubicConfigurationFunctionField_of_flat p hp 11
  letI : Infinite F := CharZero.infinite F
  let P := p.map a₁₁.hom
  let hP := hp.map a₁₁.hom
  let P0 := cubicConfigurationCoefficientChange_ne_zero p hp 11 a₁₁ hp0
  letI : Smooth (hypersurfaceToBase P hP) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 11 a₁₁
  let base := hypersurfaceToBase P hP
  let D₁₁ := cubicConfigurationGenericFiniteSubscheme p hp 11 a₁₁ ha₁₁
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 11 a₁₁ ha₁₁
  letI : IsFinite pD := D₁₁.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  let L := Γ(D₁₁.val.subscheme, ⊤)
  letI : Field L :=
    (cubicConfigurationGenericFiniteSubscheme_isField p hp 11 a₁₁ ha₁₁ (0 : Fin 11)).toField
  letI : Algebra F L := finiteSchemeCoefficientAlgebra pD
  letI : FiniteDimensional F L := finiteSchemeCoefficient_finite pD
  let i₁₁ := finiteSubschemeDatumSpecMap base D₁₁
  let hi₁₁ := finiteSubschemeDatumSpecMap_toBase base D₁₁
  let hL : finrank F L = 11 := by
    rw [finiteSchemeCoefficient_finrank]
    exact finiteSubschemeDatum_finiteSchemeRank base D₁₁
  change CubicFieldChartSerreGoodData (F := F) (L := L) P hP i₁₁ at hGood
  exact cubicFieldChartSerreGoodData_genericThree_effectiveEight
    (F := F) (L := L) P hP P0 i₁₁ hi₁₁ hL hGood

end PfaffianDescent
