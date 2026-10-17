import PfaffianDescent.VoisinSelectedEightCoordinateSectionWitness
import PfaffianDescent.VoisinSelectedCubicCoefficientMap
import PfaffianDescent.VoisinGenericTripleSelectedPoints
import PfaffianDescent.VoisinQuadraticMinorDistinctPoints

/-!
# The selected actual family is generically finite

The affine ordered configuration chart carries the cubic coefficients and
its selected point is a section over the coefficient field.  The cubic and
two regular quadratic-kernel equations therefore form a genuinely finite
family on a neighborhood of the determinant-open generic point.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_generic_eight_selected_actual_finiteNeighborhood
    (K : Type u) [Field K] [CharZero K]
    {L : Type u} [Field L] [CharZero L] [IsAlgClosed L]
    (φ : FractionRing (CubicTensorCoefficients K) →+* L) :
    let p := ((genericCubicTensor K).map φ).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      ((genericCubicTensor K).map φ)
    ∃ (hInt : IsIntegral (cubicConfigurationBase p hp 8)),
    letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
    ∃ (U Q : Scheme.{u}) (_ : IsAffine U) (_ : IsAffine Q)
      (hU : IsIntegral U) (hQ : IsIntegral Q)
      (i : U ⟶ (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left)
      (j : Q ⟶ cubicConfigurationBase p hp 8)
      (r : U ⟶ Q)
      (hi : IsOpenImmersion i) (hj : IsOpenImmersion j)
      (hsurjr : Surjective r)
      (hintr : IsIntegralHom r)
      (hfinr : IsFinite r)
      (hQgeneric : genericPoint (cubicConfigurationBase p hp 8) ∈ Set.range j)
      (hcomm : i ≫ configurationQuotientMap (equationIdeal p hp) 8 = r ≫ j)
      (m : Fin 8 ↪ Monomials (Fin 4) 2)
      (c : Fin 4 → L)
      (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
      (x : Fin 8 → Fin 4 → Γ(U, ⊤))
      (hdet : quadraticMinorDet m x ≠ 0)
      (pS : MvPolynomial (Fin 4)
        (Localization.Away (quadraticMinorDet m x)))
      (hpS : pS.IsHomogeneous 3)
      (ψ : FractionRing (CubicTensorCoefficients K) →+*
        Localization.Away (quadraticMinorDet m x))
      (hpmap : pS = (genericCubicTensor K).toMvPolynomial.map ψ)
      (ellS : MvPolynomial (Fin 4)
        (Localization.Away (quadraticMinorDet m x)))
      (hellS : ellS.IsHomogeneous 1),
      letI : IsIntegral U := hU
      letI : IsDomain (Localization.Away (quadraticMinorDet m x)) :=
        Localization.Away.isDomain hdet
      ∃ hcharS : CharZero (Localization.Away (quadraticMinorDet m x)),
      letI : CharZero (Localization.Away (quadraticMinorDet m x)) := hcharS
      ∃ V : (Spec (.of (Localization.Away (quadraticMinorDet m x)))).Opens,
        genericPoint (Spec (.of (Localization.Away (quadraticMinorDet m x)))) ∈ V ∧
        IsFinite ((relativeTripleIntersectionToBase pS
          (quadraticSelectedOpenPolynomial m x 0)
          (quadraticSelectedOpenPolynomial m x 1) hpS
          (quadraticSelectedOpenPolynomial_isHomogeneous m x 0)
          (quadraticSelectedOpenPolynomial_isHomogeneous m x 1)) ∣_ V) ∧
        Function.Injective (fun k j => algebraMap Γ(U, ⊤)
          (Localization.Away (quadraticMinorDet m x)) (x k j)) ∧
        HasEightDistinctGenericTriplePoints pS
          (quadraticSelectedOpenPolynomial m x 0)
          (quadraticSelectedOpenPolynomial m x 1) hpS
          (quadraticSelectedOpenPolynomial_isHomogeneous m x 0)
          (quadraticSelectedOpenPolynomial_isHomogeneous m x 1)
          ellS hellS
          (fun k j => algebraMap Γ(U, ⊤)
            (Localization.Away (quadraticMinorDet m x)) (x k j)) ∧
        (∀ k : Fin 8,
          pS.eval (fun j => algebraMap Γ(U, ⊤)
            (Localization.Away (quadraticMinorDet m x)) (x k j)) = 0 ∧
          ∀ j : Fin 2,
            (quadraticSelectedOpenPolynomial m x j).eval
              (fun l => algebraMap Γ(U, ⊤)
                (Localization.Away (quadraticMinorDet m x)) (x k l)) = 0 ∧
          ellS.eval (fun j => algebraMap Γ(U, ⊤)
            (Localization.Away (quadraticMinorDet m x)) (x k j)) = 1) ∧
        ∃ t : Fin 8 → (U ⟶ Spec (.of
            (Away (grading (equationIdeal p hp))
              (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
                (homogeneousLinearForm c))))),
          (∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
            (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
              (homogeneousLinearForm c))
            (polynomial_class_mem_grading (equationIdeal p hp)
              (homogeneousLinearForm c)
              (homogeneousLinearForm_isHomogeneous c))
            (by decide : 0 < 1) =
            (i ≫ Over.Hom.left
              (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
              (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left) ∧
          x = pulledEightLinearChartCoordinates (equationIdeal p hp)
            (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
              (homogeneousLinearForm c))
            (polynomial_class_mem_grading (equationIdeal p hp)
              (homogeneousLinearForm c)
              (homogeneousLinearForm_isHomogeneous c)) U t ∧
          Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) ∧
          Smooth (hypersurfaceToBase p hp) ∧
          pS = p.map ((algebraMap Γ(U, ⊤)
            (Localization.Away (quadraticMinorDet m x))).comp
              (affineFunctionHom (i ≫
                (orderedFamilyConfigurationOver
                  (hypersurfaceToBase p hp) 8).hom))) := by
  dsimp only
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  obtain ⟨hsmooth, y, _, c, hc, m, D, hInt,
    U, Q, hUa, hQa, i, j, r, a, tBase, t, x, f, hm, _, _,
    hi, hj, hsurjr, hintr, hfinr, hUi, hQi, hgenericQ, hcomm,
    hEt, _, hsurj, hquad, _, _, _, _, _, _, hat, hf, hfx, hpvan, hnormone,
    _, _, ht, hxdef, htBase⟩ :=
    exists_generic_eight_selected_coordinate_sections_with_minor K φ
  letI : IsIntegral U := hUi
  letI : IsDomain Γ(U, ⊤) := inferInstance
  have hdet : quadraticMinorDet m x ≠ 0 :=
    quadraticMinorDet_ne_zero_of_specialized_unit m x f hm
  letI : IsDomain (Localization.Away (quadraticMinorDet m x)) :=
    Localization.Away.isDomain hdet
  let β := affineFunctionHom tBase
  have hβ : f.comp β = RingHom.id L := by
    rw [hf]
    exact affineFunctionHom_section_leftInverse tBase a hat
  let βS := (algebraMap Γ(U, ⊤)
    (Localization.Away (quadraticMinorDet m x))).comp β
  have hcharS : CharZero (Localization.Away (quadraticMinorDet m x)) :=
    charZero_of_injective_ringHom βS.injective
  let pS := p.map βS
  have hpS : pS.IsHomogeneous 3 :=
    (cubic_toMvPolynomial_isHomogeneous_three _).map βS
  let ψ := βS.comp φ
  have hpmap : pS = (genericCubicTensor K).toMvPolynomial.map ψ := by
    change ((genericCubicTensor K).map φ).toMvPolynomial.map βS =
      (genericCubicTensor K).toMvPolynomial.map (βS.comp φ)
    rw [← cubic_toMvPolynomial_map φ, MvPolynomial.map_map]
  let ellS := (homogeneousLinearForm c).map βS
  have hellS : ellS.IsHomogeneous 1 :=
    (homogeneousLinearForm_isHomogeneous c).map βS
  have hfinite := genericCubic_selectedOpenFrame_exists_genericFiniteNeighborhood
    K φ m x f hm y c hc hfx hsurj hquad β hβ
  obtain ⟨V, hV, hfin⟩ := hfinite
  have hpoly : (p.map β).map (algebraMap Γ(U, ⊤)
      (Localization.Away (quadraticMinorDet m x))) = pS := by
    rw [MvPolynomial.map_map]
  have hellpoly : ((homogeneousLinearForm c).map β).map
      (algebraMap Γ(U, ⊤)
        (Localization.Away (quadraticMinorDet m x))) = ellS := by
    rw [MvPolynomial.map_map]
  have hpoints (k : Fin 8) :
      pS.eval (fun j => algebraMap Γ(U, ⊤)
        (Localization.Away (quadraticMinorDet m x)) (x k j)) = 0 := by
    have h := congrArg (algebraMap Γ(U, ⊤)
      (Localization.Away (quadraticMinorDet m x))) (hpvan k)
    rw [MvPolynomial.eval₂_comp, MvPolynomial.eval₂_eq_eval_map,
      hpoly, map_zero] at h
    simpa only [Function.comp_def] using h
  have hnormalized (k : Fin 8) :
      ellS.eval (fun j => algebraMap Γ(U, ⊤)
        (Localization.Away (quadraticMinorDet m x)) (x k j)) = 1 := by
    have h := congrArg (algebraMap Γ(U, ⊤)
      (Localization.Away (quadraticMinorDet m x))) (hnormone k)
    rw [MvPolynomial.eval₂_comp, MvPolynomial.eval₂_eq_eval_map,
      hellpoly, map_one] at h
    simpa only [Function.comp_def] using h
  have hminorS : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => algebraMap Γ(U, ⊤)
        (Localization.Away (quadraticMinorDet m x)) (x k j))).det := by
    rw [← eightPointQuadraticEvaluationMinor_map]
    exact quadraticMinor_isUnit_on_principalOpen m x
  have hinj : Function.Injective (fun k j => algebraMap Γ(U, ⊤)
      (Localization.Away (quadraticMinorDet m x)) (x k j)) :=
    eightPointQuadraticEvaluationMinor_unit_injective m _ hminorS
  have hzeroS (k : Fin 8) :
      pS.eval (fun j => algebraMap Γ(U, ⊤)
        (Localization.Away (quadraticMinorDet m x)) (x k j)) = 0 ∧
      (quadraticSelectedOpenPolynomial m x 0).eval
        (fun j => algebraMap Γ(U, ⊤)
          (Localization.Away (quadraticMinorDet m x)) (x k j)) = 0 ∧
      (quadraticSelectedOpenPolynomial m x 1).eval
        (fun j => algebraMap Γ(U, ⊤)
          (Localization.Away (quadraticMinorDet m x)) (x k j)) = 0 :=
    ⟨hpoints k,
      quadraticSelectedOpenPolynomial_eval_zero m x 0 k,
      quadraticSelectedOpenPolynomial_eval_zero m x 1 k⟩
  have hEight : HasEightDistinctGenericTriplePoints pS
      (quadraticSelectedOpenPolynomial m x 0)
      (quadraticSelectedOpenPolynomial m x 1) hpS
      (quadraticSelectedOpenPolynomial_isHomogeneous m x 0)
      (quadraticSelectedOpenPolynomial_isHomogeneous m x 1)
      ellS hellS
      (fun k j => algebraMap Γ(U, ⊤)
        (Localization.Away (quadraticMinorDet m x)) (x k j)) :=
    hasEightDistinctGenericTriplePoints_of_equations
      pS (quadraticSelectedOpenPolynomial m x 0)
      (quadraticSelectedOpenPolynomial m x 1) hpS
      (quadraticSelectedOpenPolynomial_isHomogeneous m x 0)
      (quadraticSelectedOpenPolynomial_isHomogeneous m x 1)
      ellS hellS _ hzeroS hnormalized hinj
  have hps : pS = p.map ((algebraMap Γ(U, ⊤)
      (Localization.Away (quadraticMinorDet m x))).comp
        (affineFunctionHom (i ≫
          (orderedFamilyConfigurationOver
            (hypersurfaceToBase p hp) 8).hom))) := by
    rw [← htBase]
  exact ⟨hInt, U, Q, hUa, hQa, hUi, hQi,
    i, j, r, hi, hj, hsurjr, hintr, hfinr, hgenericQ, hcomm,
    m, c, D, x, hdet, pS, hpS, ψ, hpmap,
    ellS, hellS, hcharS,
    V, hV, hfin, hinj,
    hEight,
    fun k => ⟨hpoints k,
      fun j => ⟨quadraticSelectedOpenPolynomial_eval_zero m x j k,
        hnormalized k⟩⟩, t, ht, hxdef, hEt, hsmooth, hps⟩

end PfaffianDescent
