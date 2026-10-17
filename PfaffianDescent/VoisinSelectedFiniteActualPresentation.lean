import PfaffianDescent.VoisinSmoothSelectedActualEightPresentation
import PfaffianDescent.VoisinActualSelectedFrameFiberFinite

/-! A selected common chart with a finite triple-intersection
neighborhood has a finite canonical intrinsic eight-point fiber. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_actualCanonicalIntrinsicFinite_of_selectedFiniteNeighborhood
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0) [Smooth (hypersurfaceToBase p hp)]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8)
    {U Q : Scheme.{u}} [IsIntegral U] [IsIntegral Q]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i]
    (j : Q ⟶ cubicConfigurationBase p hp 8) [IsOpenImmersion j]
    (r : U ⟶ Q) [Surjective r]
    (hcomm : i ≫ configurationQuotientMap (equationIdeal p hp) 8 =
      r ≫ j)
    (ell : MvPolynomial (Fin 4) K) (hell : ell.IsHomogeneous 1)
    (t : Fin 8 → (U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)
      (polynomial_class_mem_grading (equationIdeal p hp) ell hell)
      (by decide : 0 < 1) =
        (i ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left)
    (hno : QuadraticEightNoCommonResidueFieldEquationAt
      (hsep := isSeparated_homogeneousToBase (equationIdeal p hp))
      p hp (i (genericPoint U)))
    (m : Fin 8 ↪ Monomials (Fin 4) 2) :
    let zc := Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell
    let hzc := polynomial_class_mem_grading (equationIdeal p hp) ell hell
    let x := pulledEightLinearChartCoordinates
      (equationIdeal p hp) zc hzc U t
    ∀ (hdet : quadraticMinorDet m x ≠ 0),
      let S := Localization.Away (quadraticMinorDet m x)
      letI : IsDomain S := Localization.Away.isDomain hdet
      let β : K →+* Γ(U, ⊤) := affineFunctionHom
        (i ≫ (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).hom)
      let βS : K →+* S := (algebraMap Γ(U, ⊤) S).comp β
      let pS := p.map βS
      let hpS := hp.map βS
      let q₀ := quadraticSelectedOpenPolynomial m x 0
      let q₁ := quadraticSelectedOpenPolynomial m x 1
      let hq₀ := quadraticSelectedOpenPolynomial_isHomogeneous m x 0
      let hq₁ := quadraticSelectedOpenPolynomial_isHomogeneous m x 1
      ∀ (V : (Spec (.of S)).Opens),
        genericPoint (Spec (.of S)) ∈ V →
        IsFinite ((relativeTripleIntersectionToBase
          pS q₀ q₁ hpS hq₀ hq₁) ∣_ V) →
        letI : IsSeparated (hypersurfaceToBase p hp) :=
          isSeparated_homogeneousToBase (equationIdeal p hp)
        letI : IsIntegral (projectiveConfigurationQuotientOpen
          (grading (equationIdeal p hp))
          (hypersurfaceToBase p hp) 8).toScheme :=
          isIntegral_cubicConfigurationBase_of_smooth p hp hpne
        letI : IsIntegral (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).left :=
          isIntegral_orderedCubicConfiguration_of_smooth p hp hpne
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
  let zc := Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell
  let hzc := polynomial_class_mem_grading (equationIdeal p hp) ell hell
  let x := pulledEightLinearChartCoordinates
    (equationIdeal p hp) zc hzc U t
  intro mdet
  let S := Localization.Away (quadraticMinorDet m x)
  letI : IsDomain S := Localization.Away.isDomain mdet
  let β : K →+* Γ(U, ⊤) := affineFunctionHom
    (i ≫ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).hom)
  let βS : K →+* S := (algebraMap Γ(U, ⊤) S).comp β
  let pS := p.map βS
  let hpS := hp.map βS
  let q₀ := quadraticSelectedOpenPolynomial m x 0
  let q₁ := quadraticSelectedOpenPolynomial m x 1
  let hq₀ := quadraticSelectedOpenPolynomial_isHomogeneous m x 0
  let hq₁ := quadraticSelectedOpenPolynomial_isHomogeneous m x 1
  intro V hη hfin
  letI : Smooth (hypersurfaceToBase p hp) := inferInstance
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme :=
    isIntegral_cubicConfigurationBase_of_smooth p hp hpne
  letI : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left :=
    isIntegral_orderedCubicConfiguration_of_smooth p hp hpne
  obtain ⟨hz, w, hwzc, hwt, hx⟩ :=
    exists_actualGenericEightPresentation_of_smooth_compatibleCharts
      p hp hpne a ha i j r hcomm zc hzc ell hell rfl t ht hno
  refine ⟨hz, w, ?_⟩
  let P (y : Fin 8 → Fin 4 → Γ(U, ⊤)) : Prop :=
    ∀ (hdet : quadraticMinorDet m y ≠ 0),
      let S := Localization.Away (quadraticMinorDet m y)
      letI : IsDomain S := Localization.Away.isDomain hdet
      let βS : K →+* S := (algebraMap Γ(U, ⊤) S).comp β
      let pS := p.map βS
      let hpS := hp.map βS
      let q₀ := quadraticSelectedOpenPolynomial m y 0
      let q₁ := quadraticSelectedOpenPolynomial m y 1
      let hq₀ := quadraticSelectedOpenPolynomial_isHomogeneous m y 0
      let hq₁ := quadraticSelectedOpenPolynomial_isHomogeneous m y 1
      ∀ (V : (Spec (.of S)).Opens),
        genericPoint (Spec (.of S)) ∈ V →
        IsFinite ((relativeTripleIntersectionToBase
          pS q₀ q₁ hpS hq₀ hq₁) ∣_ V) →
        IsFinite (toBase (intrinsicEightPointTripleHomogeneousIdeal
          (p.map ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
            (orderedFamilyConfigurationOver
              (hypersurfaceToBase p hp) 8).hom)).hom))
          (hp.map ((Spec.preimage (openImmersion_genericResidueLift i ≫ i ≫
            (orderedFamilyConfigurationOver
              (hypersurfaceToBase p hp) 8).hom)).hom))
          (w.canonicalVectors p hp a ha i hz)))
  have hmainW : P (pulledEightLinearChartCoordinates
      (equationIdeal p hp) w.zc w.hzc U w.t) :=
    w.canonicalIntrinsic_isFinite_of_selectedFiniteNeighborhood
      p hp a ha i hz m
  have hmainX : P x := Eq.mp (congrArg P hx) hmainW
  exact hmainX mdet V hη hfin

end PfaffianDescent
