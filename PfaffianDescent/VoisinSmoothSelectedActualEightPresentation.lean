import Mathlib.Algebra.CharZero.Infinite
import PfaffianDescent.VoisinSelectedActualEightPresentation
import PfaffianDescent.VoisinGenericCubicResidual
import PfaffianDescent.VoisinGeometricEightGoodPoint
import PfaffianDescent.VoisinSmoothEightConfigurationIntegrality

/-! Smooth finite-étale cubics supply the hypotheses for the actual
selected eight-point comparison presentation. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_actualGenericEightPresentation_of_smooth_compatibleCharts
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
    (zc : CoordinateRing (equationIdeal p hp))
    (hzc : zc ∈ grading (equationIdeal p hp) 1)
    (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1)
    (hellzc : Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell = zc)
    (t : Fin 8 → (U ⟶ Spec (.of
      (Away (grading (equationIdeal p hp)) zc))))
    (ht : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp)) zc hzc
      (by decide : 0 < 1) =
        (i ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left)
    (hno : QuadraticEightNoCommonResidueFieldEquationAt
      (hsep := isSeparated_homogeneousToBase (equationIdeal p hp))
      p hp (i (genericPoint U))) :
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
        w.zc = zc ∧ HEq w.t t ∧
        pulledEightLinearChartCoordinates (equationIdeal p hp)
          w.zc w.hzc U w.t =
          pulledEightLinearChartCoordinates (equationIdeal p hp)
            zc hzc U t := by
  dsimp only
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme := by
    change IsIntegral (cubicConfigurationBase p hp 8)
    infer_instance
  letI : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left :=
    isIntegral_orderedCubicConfiguration_of_smooth p hp hpne
  letI : Flat (toBase (equationIdeal p hp)) := by
    change Flat (hypersurfaceToBase p hp)
    infer_instance
  letI : CharZero (cubicConfigurationBase p hp 8).functionField :=
    charZero_cubicConfigurationFunctionField_of_flat p hp 8
  letI : Infinite (cubicConfigurationBase p hp 8).functionField :=
    CharZero.infinite _
  let hz := selectedOrderedChart_genericPoint_over_cubicGenericBase
    p hp i j r hcomm
  exact ⟨hz, exists_actualGenericEightPresentation_of_noCommon
    p hp a ha i hz zc hzc ell hell hellzc t ht hno⟩

/-- The selected-chart existence theorem gives a lift separately for each
of the eight labels; choose them to build one actual presentation. -/
theorem exists_actualGenericEightPresentation_of_smooth_chartLifts
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
    (ell : MvPolynomial (Fin 4) K)
    (hell : ell.IsHomogeneous 1)
    (ht : ∀ k : Fin 8,
      ∃ t : U ⟶ Spec (.of (Away (grading (equationIdeal p hp))
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell))),
        t ≫ Proj.awayι (grading (equationIdeal p hp))
          (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell)
          (polynomial_class_mem_grading (equationIdeal p hp) ell hell)
          (by decide : 0 < 1) =
          (i ≫ Over.Hom.left
            (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left) :
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
      Nonempty (ActualGenericEightPresentation p hp a ha i hz) := by
  let zc := Ideal.Quotient.mk (equationIdeal p hp).toIdeal ell
  let hzc := polynomial_class_mem_grading (equationIdeal p hp) ell hell
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  letI : IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme :=
    isIntegral_cubicConfigurationBase_of_smooth p hp hpne
  letI : IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left :=
    isIntegral_orderedCubicConfiguration_of_smooth p hp hpne
  let hz := selectedOrderedChart_genericPoint_over_cubicGenericBase
    p hp i j r hcomm
  have hgood : ∃ w : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left,
      w ∉ quadraticEightFixedFrameBadLocus p hp :=
    exists_smoothCubic_orderedEight_goodPoint p hp hpne
  have hno : QuadraticEightNoCommonResidueFieldEquationAt
      p hp (i (genericPoint U)) :=
    quadraticEightNoCommon_at_every_generic_ordered_lift_of_goodPoint
      p hp hgood (i (genericPoint U)) hz
  obtain ⟨hz, w, _, _, _⟩ :=
    exists_actualGenericEightPresentation_of_smooth_compatibleCharts
      p hp hpne a ha i j r hcomm zc hzc ell hell rfl
      (fun k => Classical.choose (ht k))
      (fun k => Classical.choose_spec (ht k)) hno
  exact ⟨hz, ⟨w⟩⟩

end PfaffianDescent
