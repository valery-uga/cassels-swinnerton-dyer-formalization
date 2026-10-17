import PfaffianDescent.VoisinGenericSelectedCanonicalIntrinsicFinite
import PfaffianDescent.VoisinActualFiniteUnorderedPencil

/-! The selected generic cubic has a finite unordered quadratic-pencil
intersection over its generic eight-point configuration field. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_genericCubic_finiteUnorderedPencil
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    ∃ hInt : IsIntegral (cubicConfigurationBase p hp 8),
      letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
      ∀ (a : CommRingCat.of L ⟶ CommRingCat.of
          (cubicConfigurationBase p hp 8).functionField)
        (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
          cubicConfigurationToBase p hp 8),
        ∃ q : Fin 2 → homogeneousSubmodule (Fin 4)
            (cubicConfigurationBase p hp 8).functionField 2,
          LinearIndependent (cubicConfigurationBase p hp 8).functionField q ∧
          IsFinite (relativeTripleIntersectionToBase
            (p.map a.hom) (q 0).1 (q 1).1
            (hp.map a.hom) (q 0).2 (q 1).2) := by
  dsimp only
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  obtain ⟨hInt, D, hEt, hsmooth, U, hU, i, hi, hdata⟩ :=
    exists_genericCubic_actualCanonicalIntrinsicFinite K φ
  refine ⟨hInt, ?_⟩
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
  intro a ha
  obtain ⟨hz, w, hfin⟩ := hdata a ha
  letI := hfin
  exact w.exists_finiteUnorderedTriple p hp a ha i hz

end PfaffianDescent
