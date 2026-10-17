import PfaffianDescent.CubicElevenPointGroundSerreEvaluationKernel
import PfaffianDescent.CubicElevenPointGroundKernelFactory

/-! The original smooth cubic constructs the actual canonical Serre
bundle with nine sections and surjective six-dimensional evaluation.
No interpolation, bundle, cover, section-rank, or evaluation input remains. -/
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

theorem exists_cubicElevenPoint_groundSerreEvaluation
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
    CubicElevenPointGroundSerreEvaluationFor p hp a ha := by
  obtain ⟨hO, hB, hdata⟩ := exists_cubicElevenPoint_groundChartKernel p hp hp0
  letI : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 11).left := hO
  letI : IsIntegral (cubicConfigurationBase p hp 11) := hB
  obtain ⟨a, ha, hkernel⟩ := hdata
  refine ⟨hO, hB, a, ha, ?_⟩
  exact cubicElevenPointGroundSerreEvaluation_of_native_kernel p hp hp0 a ha hkernel

end PfaffianDescent
