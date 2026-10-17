import PfaffianDescent.CubicElevenPointGroundSerreEvaluationData

/-! Apply the native kernel construction to the SAME actual canonical
degree-eleven point. Its field, degree, and Serre data are constructed. -/
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

abbrev cubicElevenPointGroundSerreEvaluation_of_native_kernel
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    [IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left]
    [IsIntegral (cubicConfigurationBase p hp 11)]
    (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 11).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 11 ≫
      cubicConfigurationToBase p hp 11)
    (hkernel : CubicElevenPointGroundChartKernelFor p hp a ha) := by
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
  letI : FiniteDimensional F L := finiteSchemeCoefficient_finite pD
  let i := finiteSubschemeDatumSpecMap (hypersurfaceToBase P hP) D
  have hi : i ≫ hypersurfaceToBase P hP = Spec.map (CommRingCat.ofHom (algebraMap F L)) :=
    finiteSubschemeDatumSpecMap_toBase (hypersurfaceToBase P hP) D
  exact cubicFieldChartSerreEvaluationData_of_native_kernel P hP hP0 i hi
    (cubicConfigurationGenericFiniteSubscheme_finrank p hp 11 a ha) hkernel

end PfaffianDescent
