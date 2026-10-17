import PfaffianDescent.CubicClosedPointSerrePointSplittingCubicCoverProjection
import PfaffianDescent.CubicClosedPointSerrePointSplittingComponentAlgebra
import PfaffianDescent.CubicPointTraceFieldBaseChangeNegativeTwist
import AllCharacteristics.HypersurfaceCoefficientNaturality
import PfaffianDescent.CubicClosedPointSerrePointSplittingOverIso
import PfaffianDescent.CubicConfigurationOrderedFieldComponents

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

/-- Literal actual point of the coefficient-changed cubic used by the native
unordered-support evaluator. -/
def pointSplittingCubicSerrePulledEvaluation_component (i : Fin 3) :
    Spec (.of E) ⟶ hypersurface (p.map a.hom) (hp.map a.hom) := by
  letI : Algebra (cubicConfigurationBase p hp 3).functionField E := β.toAlgebra
  let D := cubicConfigurationGenericFiniteSubscheme p hp 3 a ha
  let q := D.val.subschemeι ≫ hypersurfaceToBase (p.map a.hom) (hp.map a.hom)
  let e := pointSplittingCubicCoverIso p hp 3 c β hβ a ha
  exact pointSplittingFiniteComponentPoint q 3 e (ULift.up i) ≫ D.val.subschemeι

/-- The literal evaluator component is the SAME native labeled finite-support
component, including its exact immersion into the new cubic. -/
theorem pointSplittingCubicSerrePulledEvaluation_component_eq (i : Fin 3) :
    pointSplittingCubicSerrePulledEvaluation_component p hp c β hβ a ha i =
      cubicConfigurationOrderedFieldCoefficientChangedComponentPoint p hp 3 c β hβ a ha i ≫
        (cubicConfigurationGenericFiniteSubscheme p hp 3 a ha).val.subschemeι := by
  letI : Algebra (cubicConfigurationBase p hp 3).functionField E := β.toAlgebra
  have h := pointSplittingCubicCoverIso_component_fst p hp 3 c β hβ a ha i
  have h' := congrArg (fun v => v ≫
    (cubicConfigurationGenericFiniteSubscheme p hp 3 a ha).val.subschemeι) h
  simpa only [pointSplittingCubicSerrePulledEvaluation_component,
    pointSplittingFiniteComponentPoint, pointSplittingCubicCoverIso, Iso.trans_hom,
    cubicConfigurationCoefficientChangedBaseMap,
    cubicConfigurationOrderedFieldCoefficientChangedComponentPoint,
    cubicConfigurationOrderedFieldComponentPoint,
    projectiveConfigurationOrderedGenericComponentPoint,
    projectiveConfigurationOrderedGenericFiberToFiniteSubscheme,
    RingHom.algebraMap_toAlgebra, Category.assoc] using h'

/-- The actual new point composed with the literal coefficient map is the
SAME original ordered marked point; no comparison certificate is an input. -/
theorem pointSplittingCubicSerrePulledEvaluation_component_coefficient (i : Fin 3) :
    pointSplittingCubicSerrePulledEvaluation_component p hp c β hβ a ha i ≫
      cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp =
    (c ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 3)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 3 i).left := by
  apply (cancel_mono (hypersurfaceToAmbient p hp)).mp
  have hcoef : cubicPointTraceFieldBaseChangeCubicCoefficientMap a.hom p hp ≫
      hypersurfaceToAmbient p hp =
      hypersurfaceToAmbient (p.map a.hom) (hp.map a.hom) ≫ ambientCoefficientMap a.hom := by
    rw [← cubicPointTraceFieldBaseChangeCubicCoefficientMap_eq_projection]
    exact hypersurfaceReductionMap_comp_hypersurfaceToAmbient a.hom p hp
      (p.map a.hom) (hp.map a.hom) rfl
  rw [Category.assoc, hcoef, pointSplittingCubicSerrePulledEvaluation_component_eq]
  exact cubicConfigurationOrderedFieldCoefficientChangedComponentPoint_toMarkedPoint
    p hp 3 c β hβ a ha i

end PfaffianDescent
