import PfaffianDescent.VoisinCanonicalFiniteFamilyDegreeFour
import PfaffianDescent.VoisinGenericDegreeFourSurfaceCycle
import PfaffianDescent.VoisinEffectiveCycleGenericSpecialization

/-! Specialize the degree-four cycle from an actual finite canonical family
over an arbitrary smooth cubic back to its original ground field. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_effectiveDegreeFourCycle_of_actualCanonicalFiniteFamily
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    (D₈ : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    [Etale (D₈.val.subschemeι ≫ hypersurfaceToBase p hp)]
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i]
    (hfamily :
      letI : IsSeparated (hypersurfaceToBase p hp) :=
        isSeparated_homogeneousToBase (equationIdeal p hp)
      letI : IsIntegral (projectiveConfigurationQuotientOpen
        (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme :=
        isIntegral_cubicConfigurationBase_of_smooth p hp hpne
      letI : IsIntegral (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left :=
        isIntegral_orderedCubicConfiguration_of_smooth p hp hpne
      letI : IsIntegral (cubicConfigurationBase p hp 8) :=
        isIntegral_cubicConfigurationBase_of_smooth p hp hpne
      ActualCanonicalFiniteFamily p hp i) :
    letI : IsIntegral (cubicConfigurationBase p hp 8) :=
      isIntegral_cubicConfigurationBase_of_smooth p hp hpne
    ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
        cubicConfigurationToBase p hp 8),
      ∃ z : EffectiveZeroCycle (hypersurface p hp),
        EffectiveZeroCycle.degree (hypersurfaceToBase p hp) z = 4 := by
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme :=
    isIntegral_cubicConfigurationBase_of_smooth p hp hpne
  letI : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left :=
    isIntegral_orderedCubicConfiguration_of_smooth p hp hpne
  letI : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth p hp hpne
  letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite (cubicConfigurationBase p hp 8).functionField :=
    CharZero.infinite _
  intro a ha
  let D := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  obtain ⟨c⟩ := hfamily.exists_degreeFourComplement p hp i a ha
  obtain ⟨zη, hzη⟩ :=
    c.exists_surfaceDegreeFourCycle (p.map a.hom) (hp.map a.hom)
  exact effectiveDegreeFourCycle_of_genericEffectiveDegreeFourCycle
    p hp hpne D₈ a ha zη hzη

end PfaffianDescent
