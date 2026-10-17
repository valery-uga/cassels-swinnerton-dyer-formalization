import PfaffianDescent.VoisinGenericSelectedCanonicalIntrinsicFinite
import PfaffianDescent.VoisinActualDegreeFourFromCanonicalFinite
import PfaffianDescent.VoisinCanonicalFiniteFamilyDegreeFour

/-! The selected generic cubic has a degree-four residual cycle over its
generic eight-point configuration function field. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A degree-four residual cycle over every compatible generic coefficient
map for one integral eight-point configuration base. -/
structure GenericCubicDegreeFourFamily
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) where
  integral : IsIntegral (cubicConfigurationBase p hp 8)
  cycles :
    letI : IsIntegral (cubicConfigurationBase p hp 8) := integral
    ∀ (a : CommRingCat.of L ⟶ CommRingCat.of
        (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
        cubicConfigurationToBase p hp 8),
      let D := cubicConfigurationGenericFiniteSubscheme p hp 8 a ha
      let pD := cubicConfigurationCoefficientChangedBaseMap p hp 8 a ha
      letI : IsFinite pD := D.property.1
      letI := finiteSchemeCoefficientAlgebra pD
      Nonempty (DegreeFourTripleComplement (A := Γ(D.val.subscheme, ⊤))
        (p.map a.hom) (hp.map a.hom))

theorem exists_genericCubic_degreeFourComplement
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    Nonempty (GenericCubicDegreeFourFamily p hp) := by
  dsimp only
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  obtain ⟨hInt, D, hEt, hsmooth, U, hU, i, hi, hdata⟩ :=
    exists_genericCubic_actualCanonicalIntrinsicFinite K φ
  refine ⟨⟨hInt, ?_⟩⟩
  letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
  letI : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) := hEt
  letI : Smooth (hypersurfaceToBase p hp) := hsmooth
  letI : IsIntegral U := hU
  letI : IsOpenImmersion i := hi
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : IsIntegral (projectiveConfigurationQuotientOpen
    (grading (equationIdeal p hp))
    (hypersurfaceToBase p hp) 8).toScheme :=
    isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
      p hp (genericCubicTensor_toMvPolynomial_ne_zero_after_baseChange K φ) 8 D
  letI : IsIntegral (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left :=
    isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
      p hp (genericCubicTensor_toMvPolynomial_ne_zero_after_baseChange K φ) 8 D
  letI : Flat (toBase (equationIdeal p hp)) := by
    change Flat (hypersurfaceToBase p hp)
    infer_instance
  letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite (cubicConfigurationBase p hp 8).functionField :=
    CharZero.infinite _
  have hfamily : ActualCanonicalFiniteFamily p hp i := hdata
  intro a ha
  exact hfamily.exists_degreeFourComplement p hp i a ha

end PfaffianDescent
