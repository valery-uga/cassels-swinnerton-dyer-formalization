import PfaffianDescent.VoisinActualEightPresentation
import PfaffianDescent.VoisinGenericEightGeometricCoordinates
import PfaffianDescent.VoisinGenericEightNoCommonAtGeneric

/-! Constructing the actual eight-point comparison presentation from a
selected common chart and the generic quadratic avoidance property. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A selected common chart and no-common-quadratic condition furnish
the geometric rank-eight coordinates needed by the actual comparison. -/
theorem exists_actualGenericEightPresentation_of_noCommon
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    [Infinite (cubicConfigurationBase p hp 8).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8)
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i]
    (hz : configurationQuotientMap (equationIdeal p hp) 8
        (i (genericPoint U)) =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField))
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
    (hno : QuadraticEightNoCommonResidueFieldEquationAt p hp
      (i (genericPoint U))) :
    ∃ w : ActualGenericEightPresentation p hp a ha i hz,
      w.zc = zc ∧ HEq w.t t ∧
      pulledEightLinearChartCoordinates (equationIdeal p hp)
        w.zc w.hzc U w.t =
        pulledEightLinearChartCoordinates (equationIdeal p hp)
          zc hzc U t := by
  refine ⟨{
    zc := zc
    hzc := hzc
    ell := ell
    hell := hell
    hellzc := hellzc
    t := t
    ht := ht
    d := ?_ }, rfl, HEq.rfl, rfl⟩
  exact Classical.choice
    (exists_cubicConfigurationGenericEight_geometricCubicCoordinates_of_noCommon
      p hp a ha (i (genericPoint U)) hz hno)

/-- For an integral ordered family on a geometrically integral cubic,
the selected common chart itself furnishes the actual presentation. -/
theorem exists_actualGenericEightPresentation_of_selectedChart
    {K : Type u} [Field K] [IsAlgClosed K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (hpne : p ≠ 0)
    (hpprime : (Ideal.span ({p} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [IsSeparated (hypersurfaceToBase p hp)]
    [IsIntegral (projectiveConfigurationQuotientOpen
      (grading (equationIdeal p hp))
      (hypersurfaceToBase p hp) 8).toScheme]
    [IsIntegral (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left]
    [IsIntegral (cubicConfigurationBase p hp 8)]
    [Infinite (cubicConfigurationBase p hp 8).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase p hp 8).functionField)
    (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 8 ≫
      cubicConfigurationToBase p hp 8)
    {U : Scheme.{u}} [IsIntegral U]
    (i : U ⟶ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) [IsOpenImmersion i]
    (hz : configurationQuotientMap (equationIdeal p hp) 8
        (i (genericPoint U)) =
      (cubicConfigurationBase p hp 8).fromSpecStalk
        (genericPoint (cubicConfigurationBase p hp 8))
        (IsLocalRing.closedPoint
          (cubicConfigurationBase p hp 8).functionField))
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
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left) :
    ∃ w : ActualGenericEightPresentation p hp a ha i hz,
      w.zc = zc ∧ HEq w.t t ∧
      pulledEightLinearChartCoordinates (equationIdeal p hp)
        w.zc w.hzc U w.t =
        pulledEightLinearChartCoordinates (equationIdeal p hp)
          zc hzc U t := by
  exact exists_actualGenericEightPresentation_of_noCommon
    p hp a ha i hz zc hzc ell hell hellzc t ht
    (quadraticEightNoCommon_at_every_generic_ordered_lift
      p hp hpne hpprime (i (genericPoint U)) hz)

end PfaffianDescent
