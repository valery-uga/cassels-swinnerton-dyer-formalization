import PfaffianDescent.CubicElevenPointGroundSerreGoodInnerResidualCycle
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridGenericThreeReference
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridTwoStageCycleSpecialization
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridFactoryBridge

/-! The actual generic-eleven Serre factory, native generic-three residual,
and two checked specializations supply the closed-eleven to effective-eight
input of the degree-ten grid factory. No external Voisin geometry is supplied. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Module MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem effectiveDegreeEight_of_etaleEleven_actualNativeFactory
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (Dorig : FiniteSubschemeDatum (hypersurfaceToBase p hp) 11)
    [Etale (Dorig.val.subschemeι ≫ hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 8 := by
  obtain ⟨hO₁₁, hB₁₁, hFactory⟩ := exists_cubicElevenPoint_groundSerreGoodParameter p hp hp0
  letI : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left := hO₁₁
  letI : IsIntegral (cubicConfigurationBase p hp 11) := hB₁₁
  obtain ⟨a₁₁, ha₁₁, hGood⟩ := hFactory
  let F := (cubicConfigurationBase p hp 11).functionField
  let P := p.map a₁₁.hom
  let hP := hp.map a₁₁.hom
  letI : CharZero F := charZero_cubicConfigurationFunctionField_of_flat p hp 11
  letI : Smooth (hypersurfaceToBase P hP) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp 11 a₁₁
  obtain ⟨hB₃, hInner⟩ :=
    cubicElevenPointGroundSerreGood_innerGenericThree_effectiveEight p hp hp0 a₁₁ ha₁₁ hGood
  letI : IsIntegral (cubicConfigurationBase P hP 3) := hB₃
  obtain ⟨a₃, ha₃, zη, hη⟩ := hInner
  obtain ⟨D₃, hD₃⟩ :=
    voisinDegreeTenSelectedAvoidance_genericCoefficientChange_exists_etaleThreeDatum
      11 p hp hp0 Dorig hno a₁₁ ha₁₁
  obtain ⟨z, hz⟩ := voisinDegreeTenSelectedAvoidance_twoStageGenericCycle_specialization
    11 3 p hp hp0 Dorig a₁₁ ha₁₁ D₃ hD₃ a₃ ha₃ zη
  exact ⟨z, hz.trans hη⟩

/-- The original closed point is used only as the actual finite-etale
specialization datum. The Serre evaluation is constructed over the outer
generic-eleven field, so no arbitrary original-point evaluation is assumed. -/
theorem effectiveDegreeEight_of_closedEleven_actualNativeFactory
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (hno : ¬ ∃ s : Spec (.of K) ⟶ hypersurface p hp,
      s ≫ hypersurfaceToBase p hp = 𝟙 _)
    (x : closedPoints (hypersurface p hp))
    (hx : (hypersurfaceToBase p hp).residueDegree x.1 = 11) :
    ∃ z : EffectiveZeroCycle (hypersurface p hp),
      EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 8 := by
  let Dorig := finiteSubschemeDatumOfClosedPointOfResidueDegree (hypersurfaceToBase p hp) x 11 hx
  letI : Etale (Dorig.val.subschemeι ≫ hypersurfaceToBase p hp) :=
    finiteSubschemeDatumOfClosedPointOfResidueDegree_toBase_etale (hypersurfaceToBase p hp) x 11 hx
  exact effectiveDegreeEight_of_etaleEleven_actualNativeFactory p hp hp0 Dorig hno

/-- The checked degree-ten grid uses the actual closed-eleven residual
construction above, removing its external geometric input. -/
theorem voisinDegreeTenSelectedAvoidance_actualNative_effectiveDegreeFourFactory
    {K : Type u} [Field K] [CharZero K] : VoisinDegreeTenEffectiveDegreeFourFor K := by
  apply voisinDegreeTenSelectedAvoidance_effectiveDegreeFourFactory_of_closedEleven_effectiveEight
  intro p hp hp0 hsmooth hno x hx
  letI : Smooth (hypersurfaceToBase p hp) := hsmooth
  exact effectiveDegreeEight_of_closedEleven_actualNativeFactory p hp hp0 hno x hx

end PfaffianDescent
