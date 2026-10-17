import PfaffianDescent.VoisinSelectedActualFiniteNeighborhood
import PfaffianDescent.VoisinGenericEightToFourCycle
import PfaffianDescent.VoisinSelectedQuotientFunctionField

/-! A degree-four cycle on the selected family's generic cubic. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_selected_actual_genericCubic_degreeFourCycle
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
      (x : Fin 8 → Fin 4 → Γ(U, ⊤))
      (hdet : quadraticMinorDet m x ≠ 0)
      (pS : MvPolynomial (Fin 4)
        (Localization.Away (quadraticMinorDet m x)))
      (hpS : pS.IsHomogeneous 3)
      (ψ : FractionRing (CubicTensorCoefficients K) →+*
        Localization.Away (quadraticMinorDet m x))
      (hpmap : pS = (genericCubicTensor K).toMvPolynomial.map ψ),
      letI : IsIntegral U := hU
      letI : IsIntegral Q := hQ
      letI : IsDomain (Localization.Away (quadraticMinorDet m x)) :=
        Localization.Away.isDomain hdet
      let f := algebraMap (Localization.Away (quadraticMinorDet m x))
        (FractionRing (Localization.Away (quadraticMinorDet m x)))
      ∃ (ε : FractionRing Γ(Q, ⊤) ≃+*
          (cubicConfigurationBase p hp 8).functionField)
        (δ : FractionRing Γ(Q, ⊤) →+*
          FractionRing (Localization.Away (quadraticMinorDet m x)))
        (_ : Function.Injective δ)
        (κ : (cubicConfigurationBase p hp 8).functionField →+*
          FractionRing (Localization.Away (quadraticMinorDet m x)))
        (_ : Function.Injective κ),
        κ.comp ε.toRingHom = δ ∧
      ∃
        (z : EffectiveZeroCycle (hypersurface (pS.map f) (hpS.map f))),
        EffectiveZeroCycle.degree
          (hypersurfaceToBase (pS.map f) (hpS.map f)) z = 4 := by
  dsimp only
  let p := ((genericCubicTensor K).map φ).toMvPolynomial
  let hp := cubic_toMvPolynomial_isHomogeneous_three
    ((genericCubicTensor K).map φ)
  obtain ⟨hInt, U, Q, hUa, hQa, hUi, hQi, i, j, r,
    hi, hj, hsurjr, hintr, hfinr, hQgeneric, hcomm,
    m, c, D, x, hdet, pS, hpS, ψ, hpmap, ellS, hellS,
    hcharS, V, hV, hfin, _, hEight, _, _⟩ :=
    exists_generic_eight_selected_actual_finiteNeighborhood K φ
  letI : IsIntegral U := hUi
  letI : IsIntegral Q := hQi
  letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
  letI : IsOpenImmersion j := hj
  letI : Surjective r := hsurjr
  letI : IsDomain (Localization.Away (quadraticMinorDet m x)) :=
    Localization.Away.isDomain hdet
  letI : CharZero (Localization.Away (quadraticMinorDet m x)) := hcharS
  letI : CharZero (FractionRing (Localization.Away (quadraticMinorDet m x))) :=
    IsFractionRing.charZero_of_isFractionRing
      (Localization.Away (quadraticMinorDet m x))
  letI : Infinite (FractionRing (Localization.Away (quadraticMinorDet m x))) :=
    inferInstance
  letI := hfin
  obtain ⟨z, hz⟩ :=
    genericCubic_exists_degreeFourCycle_of_selected_finiteNeighborhood
      pS
      (quadraticSelectedOpenPolynomial m x 0)
      (quadraticSelectedOpenPolynomial m x 1)
      hpS
      (quadraticSelectedOpenPolynomial_isHomogeneous m x 0)
      (quadraticSelectedOpenPolynomial_isHomogeneous m x 1)
      ellS hellS
      (fun k j => algebraMap Γ(U, ⊤)
        (Localization.Away (quadraticMinorDet m x)) (x k j))
      hEight V hV
  let δ := affineSurjectiveIntegral_localizedFractionMap
    r (quadraticMinorDet m x) hdet
  let ε := affineOpenImmersion_fractionEquivFunctionField j
  have hδ : Function.Injective δ :=
    affineSurjectiveIntegral_localizedFractionMap_injective
      r (quadraticMinorDet m x) hdet
  let κ := δ.comp ε.symm.toRingHom
  have hκ : Function.Injective κ := hδ.comp ε.symm.injective
  have hκδ : κ.comp ε.toRingHom = δ := by
    ext a
    simp [κ]
  exact ⟨hInt, U, Q, hUa, hQa, hUi, hQi,
    i, j, r, hi, hj, hsurjr, hintr, hfinr, hQgeneric, hcomm,
    m, x, hdet, pS, hpS, ψ, hpmap, ε, δ, hδ, κ, hκ, hκδ, z, hz⟩

end PfaffianDescent
