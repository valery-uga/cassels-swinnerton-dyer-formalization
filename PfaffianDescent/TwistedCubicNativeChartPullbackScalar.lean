import PfaffianDescent.NativeOpenPullbackUnitScalar
import PfaffianDescent.TwistedCubicNativePositivePullbackCharts
import AllCharacteristics.SpecGlobalSectionEvaluation

/-! SOURCE ONLY. The original twisted-cubic chart maps are genuine open
immersions, and their actual sheaf-of-functions maps transport the end ratio
to the cube of the line ratio. No bundle/gluing certificate is assumed. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))

/-- The literal scheme chart square before composing with the ambient embedding. -/
theorem standardTwistedCubicNativeChartMorphism_toCurve (b : Bool) :
    standardTwistedCubicNativeChartMorphism (K := K) b ≫
      chartι I (if b then 3 else 0) =
    chartι L b ≫ standardProjectiveLineToTwistedCubic (K := K) := by
  cases b
  · exact (standardProjectiveLineChartZero_toTwistedCubic (K := K)).symm
  · exact (standardProjectiveLineChartThree_toTwistedCubic (K := K)).symm

/-- The internally constructed chart coefficient morphism is an actual open
immersion because the original parametrization is the proved scheme Iso. -/
theorem standardTwistedCubicNativeChartMorphism_isOpenImmersion (b : Bool) :
    IsOpenImmersion (standardTwistedCubicNativeChartMorphism (K := K) b) := by
  letI : IsIso (standardProjectiveLineToTwistedCubic (K := K)) := by
    change IsIso (standardTwistedCubicProjectiveLineIso (K := K)).inv
    infer_instance
  let j := chartι I (if b then 3 else 0)
  let a := standardTwistedCubicNativeChartMorphism (K := K) b
  haveI : IsOpenImmersion (a ≫ j) := by
    rw [show a ≫ j = chartι L b ≫
      standardProjectiveLineToTwistedCubic (K := K) from
      standardTwistedCubicNativeChartMorphism_toCurve b]
    infer_instance
  exact IsOpenImmersion.of_comp a j

/-- Exact actual structure-sheaf image of the first end-ratio section. -/
theorem standardTwistedCubicNativeChartMorphism_false_appTop_endRatio :
    (standardTwistedCubicNativeChartMorphism (K := K) false).appTop.hom
      ((Scheme.ΓSpecIso (.of (ChartRing I 0))).inv.hom (chartCoordinate I 0 3)) =
    (Scheme.ΓSpecIso (.of (ChartRing L false))).inv.hom
      (chartCoordinate L false true ^ 3) := by
  have h := AllCharacteristics.specMap_appTop_globalSectionsIso_apply
    (standardTwistedCubicNativeChartCoefficientMap (K := K) false) (chartCoordinate I 0 3)
  rw [standardTwistedCubicNativeChartCoefficientMap_false_endRatio] at h
  exact h

/-- Exact actual structure-sheaf image of the last end-ratio section. -/
theorem standardTwistedCubicNativeChartMorphism_true_appTop_endRatio :
    (standardTwistedCubicNativeChartMorphism (K := K) true).appTop.hom
      ((Scheme.ΓSpecIso (.of (ChartRing I 3))).inv.hom (chartCoordinate I 3 0)) =
    (Scheme.ΓSpecIso (.of (ChartRing L true))).inv.hom
      (chartCoordinate L true false ^ 3) := by
  have h := AllCharacteristics.specMap_appTop_globalSectionsIso_apply
    (standardTwistedCubicNativeChartCoefficientMap (K := K) true) (chartCoordinate I 3 0)
  rw [standardTwistedCubicNativeChartCoefficientMap_true_endRatio] at h
  exact h

end PfaffianDescent.QuarticNet
