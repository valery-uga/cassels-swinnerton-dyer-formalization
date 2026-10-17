import PfaffianDescent.VoisinEffectiveCycleGenericSpecialization
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false in
theorem voisinDegreeTenSelectedAvoidance_twoStageGenericCycle_specialization
    {K : Type u} [Field K] [CharZero K] (n m : ℕ)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (D₁ : FiniteSubschemeDatum (hypersurfaceToBase p hp) n)
    [Etale (D₁.val.subschemeι ≫ hypersurfaceToBase p hp)] :
    letI : IsIntegral (cubicConfigurationBase p hp n) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 n D₁
    ∀ (a₁ : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp n).functionField)
      (ha₁ : Spec.map a₁ = cubicConfigurationGenericBaseMap p hp n ≫ cubicConfigurationToBase p hp n)
      (D₂ : FiniteSubschemeDatum (hypersurfaceToBase (p.map a₁.hom) (hp.map a₁.hom)) m)
      (_ : Etale (D₂.val.subschemeι ≫ hypersurfaceToBase (p.map a₁.hom) (hp.map a₁.hom))),
    let P := p.map a₁.hom
    let hP := hp.map a₁.hom
    letI : CharZero (cubicConfigurationBase p hp n).functionField :=
      charZero_cubicConfigurationFunctionField_of_flat p hp n
    letI : Smooth (hypersurfaceToBase P hP) :=
      smooth_cubicConfigurationGenericCoefficientChange p hp n a₁
    let P0 := cubicConfigurationCoefficientChange_ne_zero p hp n a₁ hp0
    letI : IsIntegral (cubicConfigurationBase P hP m) :=
      isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme P hP P0 m D₂
    ∀ (a₂ : CommRingCat.of (cubicConfigurationBase p hp n).functionField ⟶
        CommRingCat.of (cubicConfigurationBase P hP m).functionField)
      (ha₂ : Spec.map a₂ = cubicConfigurationGenericBaseMap P hP m ≫ cubicConfigurationToBase P hP m)
      (zη : EffectiveZeroCycle (hypersurface (P.map a₂.hom) (hP.map a₂.hom))),
      ∃ z : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z =
          EffectiveZeroCycle.degree (hypersurfaceToBase (P.map a₂.hom) (hP.map a₂.hom)) zη := by
  letI : IsIntegral (cubicConfigurationBase p hp n) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme p hp hp0 n D₁
  intro a₁ ha₁ D₂ hD₂
  letI : Etale (D₂.val.subschemeι ≫ hypersurfaceToBase (p.map a₁.hom) (hp.map a₁.hom)) := hD₂
  letI : CharZero (cubicConfigurationBase p hp n).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp n
  let P := p.map a₁.hom
  let hP := hp.map a₁.hom
  letI : Smooth (hypersurfaceToBase P hP) :=
    smooth_cubicConfigurationGenericCoefficientChange p hp n a₁
  have P0 := cubicConfigurationCoefficientChange_ne_zero p hp n a₁ hp0
  letI : IsIntegral (cubicConfigurationBase P hP m) :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme P hP P0 m D₂
  dsimp only
  intro a₂ ha₂ zη
  obtain ⟨z₁, hz₁⟩ := effectiveCycle_of_genericEffectiveCycle m P hP P0 D₂ a₂ ha₂ zη
  obtain ⟨z, hz⟩ := effectiveCycle_of_genericEffectiveCycle n p hp hp0 D₁ a₁ ha₁ z₁
  exact ⟨z, hz.trans hz₁⟩
end PfaffianDescent
