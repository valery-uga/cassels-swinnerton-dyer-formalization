import PfaffianDescent.CubicElevenPointGroundSerrePlaneKernel

/-! The original smooth cubic constructs its actual canonical Serre
bundle, native evaluation, and integral plane incidence with retained support point.
No chart, interpolation, bundle, rank, or geometric-integrality certificate
is assumed by this endpoint. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

local instance {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    [hO : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left] :
    IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 11).left := hO

theorem exists_cubicElevenPoint_groundSerrePlane
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    ∃ (hO : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left)
      (hB : IsIntegral (cubicConfigurationBase p hp 11)),
    letI := hO
    letI := hB
    ∃ (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 11).functionField)
      (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 11 ≫
        cubicConfigurationToBase p hp 11),
    CubicElevenPointGroundSerrePlaneFor p hp a ha := by
  obtain ⟨hO, hB, hdata⟩ := exists_cubicElevenPoint_groundSerreEvaluation p hp hp0
  letI : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left := hO
  letI : IsIntegral (cubicConfigurationBase p hp 11) := hB
  obtain ⟨a, ha, hEval⟩ := hdata
  refine ⟨hO, hB, a, ha, ?_⟩
  exact cubicElevenPointGroundSerrePlane_of_actual_evaluation p hp hp0 a ha hEval

end PfaffianDescent
