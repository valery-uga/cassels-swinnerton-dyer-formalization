import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerrePulledEvaluationBase
import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerreRestriction
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicCoefficientSerre
import PfaffianDescent.SerreActualPulledEvaluationSurjective

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

/-- Original actual marked-point evaluation under the native composed field
embedding; its structural point equations are proved internally. -/
def pointSplittingCubicSerrePulledEvaluation_originalEvaluator
    (M : (hypersurface p hp).Modules) := by
  letI : Algebra K E := (β.comp a.hom).toAlgebra
  exact cubicClosedPointSerreSurfaceJetCotangent_threePointSectionEvaluationTensor
    (hypersurfaceToBase p hp)
    (fun i => (c ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 i).left)
    (fun i => pointSplittingCubicSerrePulledEvaluation_original_base p hp c β hβ a ha i) M

/-- Actual original marked-point surjectivity transfers to the literal pulled
Serre bundle and SAME unordered degree-three support components. -/
theorem pointSplittingCubicSerrePulledEvaluation_surjective
    {N : (hypersurface p hp).Modules} (e : SerreExtensionData (hypersurface p hp) N)
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (honto : Function.Surjective
      (pointSplittingCubicSerrePulledEvaluation_originalEvaluator p hp c β hβ a ha
        (show _ from e.E))) :
    Function.Surjective
      (pointSplittingCubicSerreGlobalTripleEvaluator p hp c β hβ a ha
        (serreIncidenceCubicCoefficientPulledSerre a.hom p hp e C)) := by
  letI : Algebra K E := (β.comp a.hom).toAlgebra
  letI : Algebra (cubicConfigurationBase p hp 3).functionField E := β.toAlgebra
  have h := serreActualPulledEvaluation_surjective
    (hypersurfaceToBase p hp)
    (hypersurfaceToBase (p.map a.hom) (hp.map a.hom))
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp)
    (pointSplittingCubicSerrePulledEvaluation_component p hp c β hβ a ha)
    (fun i => (c ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 i).left)
    (fun i => pointSplittingCubicSerrePulledEvaluation_component_coefficient p hp c β hβ a ha i)
    (fun i => pointSplittingCubicSerrePulledEvaluation_component_base p hp c β hβ a ha i)
    (fun i => pointSplittingCubicSerrePulledEvaluation_original_base p hp c β hβ a ha i)
    (show _ from e.E) honto
  exact h

end PfaffianDescent
