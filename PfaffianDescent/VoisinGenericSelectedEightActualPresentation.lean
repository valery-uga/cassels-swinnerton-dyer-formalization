import PfaffianDescent.VoisinGenericSelectedEightChartPackage

/-! Every generic selected chart package yields the actual eight-point
presentation over the cubic configuration function field. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem SmoothCompatibleEightCharts.exists_actualPresentation
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (w : SmoothCompatibleEightCharts p hp) :
    letI : Smooth (hypersurfaceToBase p hp) := w.smooth
    letI : Etale (w.D.val.subschemeι ≫ hypersurfaceToBase p hp) := w.etale
    letI : IsIntegral (cubicConfigurationBase p hp 8) := w.baseIntegral
    letI : IsIntegral w.U := w.integralU
    letI : IsIntegral w.Q := w.integralQ
    letI : IsOpenImmersion w.i := w.openI
    letI : IsOpenImmersion w.j := w.openJ
    letI : Surjective w.r := w.surjectiveR
    ∀ (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
        cubicConfigurationToBase p hp 8),
      letI : IsSeparated (hypersurfaceToBase p hp) :=
        isSeparated_homogeneousToBase (equationIdeal p hp)
      letI : IsIntegral (projectiveConfigurationQuotientOpen
        (grading (equationIdeal p hp))
        (hypersurfaceToBase p hp) 8).toScheme :=
        isIntegral_cubicConfigurationBase_of_smooth_of_finiteEtaleSubscheme
          p hp w.hpne 8 w.D
      letI : IsIntegral (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).left :=
        isIntegral_orderedCubicConfiguration_of_smooth_of_finiteEtaleSubscheme
          p hp w.hpne 8 w.D
      ∃ hz : configurationQuotientMap (equationIdeal p hp) 8
          (w.i (genericPoint w.U)) =
        (cubicConfigurationBase p hp 8).fromSpecStalk
          (genericPoint (cubicConfigurationBase p hp 8))
          (IsLocalRing.closedPoint
            (cubicConfigurationBase p hp 8).functionField),
        Nonempty (ActualGenericEightPresentation p hp a ha w.i hz) := by
  dsimp only
  letI : Smooth (hypersurfaceToBase p hp) := w.smooth
  letI : Etale (w.D.val.subschemeι ≫ hypersurfaceToBase p hp) := w.etale
  letI : IsIntegral (cubicConfigurationBase p hp 8) := w.baseIntegral
  letI : IsIntegral w.U := w.integralU
  letI : IsIntegral w.Q := w.integralQ
  letI : IsOpenImmersion w.i := w.openI
  letI : IsOpenImmersion w.j := w.openJ
  letI : Surjective w.r := w.surjectiveR
  intro a ha
  exact exists_actualGenericEightPresentation_of_smooth_chartLifts
    p hp w.hpne a ha w.i w.j w.r w.hcomm w.ell w.hell w.lifts

end PfaffianDescent
