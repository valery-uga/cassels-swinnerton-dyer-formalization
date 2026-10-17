import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicSerrePulledEvaluationPoints

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

/-- Actual new component structure map uses the unordered-field embedding. -/
theorem pointSplittingCubicSerrePulledEvaluation_component_base (i : Fin 3) :
    pointSplittingCubicSerrePulledEvaluation_component p hp c β hβ a ha i ≫
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom) =
    Spec.map (CommRingCat.ofHom β) := by
  rw [pointSplittingCubicSerrePulledEvaluation_component_eq]
  exact cubicConfigurationOrderedFieldCoefficientChangedComponentPoint_toBase
    p hp 3 c β hβ a ha i

include hβ ha in
/-- The original ordered point is over the composed genuine coefficient map,
derived from the native new point and coefficient squares. -/
theorem pointSplittingCubicSerrePulledEvaluation_original_base (i : Fin 3) :
    ((c ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 i).left) ≫
        hypersurfaceToBase p hp =
    Spec.map (CommRingCat.ofHom (β.comp a.hom)) := by
  rw [← pointSplittingCubicSerrePulledEvaluation_component_coefficient p hp c β hβ a ha i]
  have hcoef : cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp ≫
      hypersurfaceToBase p hp =
      hypersurfaceToBase (p.map a.hom) (hp.map a.hom) ≫ Spec.map a := by
    rw [← cubicPointTraceFieldBaseChangeCubicCoefficientMap_eq_projection]
    exact hypersurfaceReductionMap_toBase a.hom p hp
      (p.map a.hom) (hp.map a.hom) rfl
  rw [Category.assoc, hcoef, ← Category.assoc,
    pointSplittingCubicSerrePulledEvaluation_component_base, ← Spec.map_comp]
  rfl

end PfaffianDescent
