import PfaffianDescent.VoisinActualEightPresentationExistence
import PfaffianDescent.VoisinSelectedGenericBasePoint

/-! The compatible selected ordered and unordered charts supply the
actual generic eight-point comparison presentation. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem exists_actualGenericEightPresentation_of_compatibleCharts
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
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left) :
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
  let hz := selectedOrderedChart_genericPoint_over_cubicGenericBase
    p hp i j r hcomm
  exact ⟨hz, exists_actualGenericEightPresentation_of_selectedChart
    p hp hpne hpprime a ha i hz zc hzc ell hell hellzc t ht⟩

end PfaffianDescent
