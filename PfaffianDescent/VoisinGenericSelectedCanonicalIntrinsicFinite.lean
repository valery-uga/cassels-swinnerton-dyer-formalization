import PfaffianDescent.VoisinSelectedActualFiniteNeighborhood
import PfaffianDescent.VoisinSelectedFiniteActualPresentation

/-! The selected generic cubic has a finite canonical intrinsic
eight-point scheme at its actual ordered generic point. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_genericCubic_actualCanonicalIntrinsicFinite
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    ∃ (hInt : IsIntegral (cubicConfigurationBase p hp 8))
      (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
      (hEt : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp))
      (hsmooth : Smooth (hypersurfaceToBase p hp))
      (U : Scheme.{u}) (hU : IsIntegral U)
      (i : U ⟶ (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left)
      (hi : IsOpenImmersion i),
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
      ∀ (a : CommRingCat.of L ⟶ CommRingCat.of
          (cubicConfigurationBase p hp 8).functionField)
        (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
        ∃ hz : configurationQuotientMap (equationIdeal p hp) 8
            (i (genericPoint U)) =
          (cubicConfigurationBase p hp 8).fromSpecStalk
            (genericPoint (cubicConfigurationBase p hp 8))
            (IsLocalRing.closedPoint
              (cubicConfigurationBase p hp 8).functionField),
          ∃ w : ActualGenericEightPresentation p hp a ha i hz,
            IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
              (p.map ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
                (orderedFamilyConfigurationOver
                  (hypersurfaceToBase p hp) 8).hom)).hom))
              (hp.map ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
                (orderedFamilyConfigurationOver
                  (hypersurfaceToBase p hp) 8).hom)).hom))
              (w.canonicalVectors p hp a ha i hz))) := by
  dsimp only
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  obtain ⟨hInt, U, Q, hUa, hQa, hUi, hQi, i, j, r,
    hi, hj, hsurjr, hintr, hfinr, hQgeneric, hcomm,
    m, c, D, x, hdet, pS, hpS, ψ, hpmap, ellS, hellS,
    hcharS, V, hη, hfin, hinj, hEight, hpoints,
    t, ht, hxdef, hEt, hsmooth, hps⟩ :=
    exists_generic_eight_selected_actual_finiteNeighborhood K φ
  refine ⟨hInt, D, hEt, hsmooth, U, hUi, i, hi, ?_⟩
  letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
  letI : IsIntegral U := hUi
  letI : IsIntegral Q := hQi
  letI : IsOpenImmersion i := hi
  letI : IsOpenImmersion j := hj
  letI : Surjective r := hsurjr
  letI : Smooth (hypersurfaceToBase p hp) := hsmooth
  letI : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) := hEt
  letI : IsDomain (Localization.Away (quadraticMinorDet m x)) :=
    Localization.Away.isDomain hdet
  intro a ha
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
  let hz := selectedOrderedChart_genericPoint_over_cubicGenericBase
    p hp i j r hcomm
  have hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) L))).IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic p hp
      (genericCubicTensor_toMvPolynomial_ne_zero_after_baseChange K φ)
  have hno : QuadraticEightNoCommonResidueFieldEquationAt
      p hp (i (genericPoint U)) :=
    quadraticEightNoCommon_at_every_generic_ordered_lift
      p hp (genericCubicTensor_toMvPolynomial_ne_zero_after_baseChange K φ)
      hpprime (i (genericPoint U)) hz
  have hres := exists_actualCanonicalIntrinsicFinite_of_selectedFiniteNeighborhood
    p hp (genericCubicTensor_toMvPolynomial_ne_zero_after_baseChange K φ)
    a ha i j r hcomm
    (homogeneousLinearForm c)
    (homogeneousLinearForm_isHomogeneous c) t ht hno m
  subst x
  clear hpmap
  subst pS
  refine hres hdet V hη ?_
  exact hfin

end PfaffianDescent
