import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsNativeSource
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsNativeTarget
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreGroundKernelOriginalSectionsEvaluationSquare

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
variable {K E : Type u} [Field K] [Field E]
variable (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
variable [hB : IsIntegral (cubicConfigurationBase p hp 3)]
local instance : IsIntegral (projectiveConfigurationQuotientOpen
    (grading (equationIdeal p hp)) (toBase (equationIdeal p hp)) 3).toScheme := hB
variable [hordered : IsIntegral (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left]
local instance : IsIntegral (orderedFamilyConfigurationOver (toBase (equationIdeal p hp)) 3).left := hordered
variable (c : Spec (.of E) ⟶ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 3).left)
variable (β : (cubicConfigurationBase p hp 3).functionField →+* E)
variable (hβ : Spec.map (CommRingCat.ofHom β) ≫
    (cubicConfigurationBase p hp 3).fromSpecStalk
      (genericPoint (cubicConfigurationBase p hp 3)) =
    c ≫ configurationQuotientMap (equationIdeal p hp) 3)
variable (a : CommRingCat.of K ⟶ CommRingCat.of (cubicConfigurationBase p hp 3).functionField)
variable (ha : Spec.map a = cubicConfigurationGenericBaseMap p hp 3 ≫
    cubicConfigurationToBase p hp 3)


open ProjectiveNegativeTwist

theorem pointSplittingCubicSerreGroundKernel_nativeEvaluationSquare
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver (hypersurfaceToBase p hp) e.E)] :
    (pointSplittingCubicSerreGroundKernel_nativeOriginalPointGammaEquiv p hp c β hβ a ha e).toLinearMap.comp
      ((pointSplittingCubicSerreGlobalTripleEvaluator p hp c β hβ a ha
        (serreIncidenceCubicCoefficientPulledSerre a.hom p hp e C)).comp
        (pointSplittingCubicSerreGroundKernel_nativeOriginalSectionsTensorEquiv p hp β a e C).symm.toLinearMap) =
    pointSplittingCubicSerrePulledEvaluation_originalEvaluator p hp c β hβ a ha e.E := by
  let F : Type u := (cubicConfigurationBase p hp 3).functionField
  letI : Algebra K F := a.hom.toAlgebra
  letI : Algebra F E := β.toAlgebra
  letI : Algebra K E := (β.comp a.hom).toAlgebra
  letI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  exact pointSplittingCubicSerreGroundKernel_originalSections_evaluation_square
    p hp e C
    (pointSplittingCubicSerrePulledEvaluation_component p hp c β hβ a ha)
    (fun i => (c ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 i).left)
    (fun i => pointSplittingCubicSerrePulledEvaluation_component_coefficient p hp c β hβ a ha i)
    (fun i => pointSplittingCubicSerrePulledEvaluation_component_base p hp c β hβ a ha i)
    (fun i => pointSplittingCubicSerrePulledEvaluation_original_base p hp c β hβ a ha i)

end PfaffianDescent
