import PfaffianDescent.NativePositiveQuotientChartPullbackUnit
import PfaffianDescent.QuarticTwistedCubicProjectiveLine
import PfaffianDescent.ActualAmbientPositiveTwistQuotientIso

/-! SOURCE ONLY. Actual two-chart local identifications for pullback of
ambient O(1) by the EXISTING twisted-cubic parametrization, and native O_P1(3).
Both maps and sheaf objects are original. This is not the global gluing endpoint. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))
local notation "PS" => homogeneousSubmodule (Fin 4) K

/-- The SAME actual standard parametrization followed by its ambient embedding. -/
def standardTwistedCubicAmbientParametrization : scheme L ⟶ Proj PS :=
  standardProjectiveLineToTwistedCubic (K := K) ≫ quotientProjMap I

/-- The actual coefficient map on each original line/cubic chart. -/
def standardTwistedCubicNativeChartCoefficientMap (b : Bool) :
    ChartRing I (if b then 3 else 0) →+* ChartRing L b := by
  cases b
  · exact standardTwistedCubicChartZeroToLineChart (K := K)
  · exact standardTwistedCubicChartThreeToLineChart (K := K)

/-- The actual scheme chart morphism, with no replacement coordinate map. -/
def standardTwistedCubicNativeChartMorphism (b : Bool) :
    Spec (.of (ChartRing L b)) ⟶ Spec (.of (ChartRing I (if b then 3 else 0))) :=
  Spec.map (CommRingCat.ofHom (standardTwistedCubicNativeChartCoefficientMap (K := K) b))

/-- Literal original chart factorization of the actual ambient parametrization. -/
theorem standardTwistedCubicAmbientParametrization_nativeChart_factorization (b : Bool) :
    chartι L b ≫ standardTwistedCubicAmbientParametrization (K := K) =
      standardTwistedCubicNativeChartMorphism (K := K) b ≫
        (chartι I (if b then 3 else 0) ≫ quotientProjMap I) := by
  cases b
  · change chartι L false ≫
      (standardProjectiveLineToTwistedCubic (K := K) ≫ quotientProjMap I) = _
    rw [← Category.assoc, standardProjectiveLineChartZero_toTwistedCubic, Category.assoc]
    rfl
  · change chartι L true ≫
      (standardProjectiveLineToTwistedCubic (K := K) ≫ quotientProjMap I) = _
    rw [← Category.assoc, standardProjectiveLineChartThree_toTwistedCubic, Category.assoc]
    rfl

/-- Native pullback of the ORIGINAL ambient O(1) on an actual cubic chart. -/
def standardTwistedCubicAmbientPositiveOne_nativeChartUnitIso (j : Fin 4) :
    (Scheme.Modules.pullback (chartι I j ≫ quotientProjMap I)).obj
      (positiveSheafOfModules PS 1) ≅
      SheafOfModules.unit (Spec (.of (ChartRing I j))).ringCatSheaf :=
  (Scheme.Modules.pullbackComp (chartι I j) (quotientProjMap I)).symm.app
      (positiveSheafOfModules PS 1) ≪≫
    (Scheme.Modules.pullback (chartι I j)).mapIso (actualAmbientPositiveTwistQuotientIso I 1) ≪≫
    positiveQuotientNativeChartPullbackUnitIso I j 1

/-- Each actual line chart gives the native frame of pullback ambient O(1). -/
def standardTwistedCubicAmbientPositiveOne_pullback_nativeChartUnitIso (b : Bool) :
    (Scheme.Modules.pullback (chartι L b)).obj
      ((Scheme.Modules.pullback (standardTwistedCubicAmbientParametrization (K := K))).obj
        (positiveSheafOfModules PS 1)) ≅
      SheafOfModules.unit (Spec (.of (ChartRing L b))).ringCatSheaf :=
  pullbackChartUnitIso_of_actual_factorization
    (standardTwistedCubicAmbientParametrization (K := K)) (chartι L b)
    (standardTwistedCubicNativeChartMorphism (K := K) b)
    (chartι I (if b then 3 else 0) ≫ quotientProjMap I)
    (standardTwistedCubicAmbientParametrization_nativeChart_factorization b)
    (positiveSheafOfModules PS 1)
    (standardTwistedCubicAmbientPositiveOne_nativeChartUnitIso (if b then 3 else 0))

/-- Native O_P1(3), using the SAME line grading, on its SAME actual chart. -/
def standardProjectiveLinePositiveThree_nativeChartUnitIso (b : Bool) :
    (Scheme.Modules.pullback (chartι L b)).obj
      (positiveSheafOfModules (grading L) 3) ≅
      SheafOfModules.unit (Spec (.of (ChartRing L b))).ringCatSheaf :=
  positiveQuotientNativeChartPullbackUnitIso L b 3

/-- Concrete local comparison on BOTH original charts. Global gluing needs
its genuine frame transition compatibility, not a supplied global Iso. -/
def standardTwistedCubicPositiveOnePullback_positiveThree_nativeChartIso (b : Bool) :
    (Scheme.Modules.pullback (chartι L b)).obj
      ((Scheme.Modules.pullback (standardTwistedCubicAmbientParametrization (K := K))).obj
        (positiveSheafOfModules PS 1)) ≅
      (Scheme.Modules.pullback (chartι L b)).obj (positiveSheafOfModules (grading L) 3) :=
  standardTwistedCubicAmbientPositiveOne_pullback_nativeChartUnitIso b ≪≫
    (standardProjectiveLinePositiveThree_nativeChartUnitIso b).symm

/-- The literal end-coordinate frame ratio pulls to the CUBE of the actual
line ratio; this carries the true degree scaling, not a polynomial dimension. -/
theorem standardTwistedCubicNativeChartCoefficientMap_false_endRatio :
    standardTwistedCubicNativeChartCoefficientMap (K := K) false (chartCoordinate I 0 3) =
      chartCoordinate L false true ^ 3 := by
  exact standardTwistedCubicChartZeroToLineChart_coordinate (K := K) 3

theorem standardTwistedCubicNativeChartCoefficientMap_true_endRatio :
    standardTwistedCubicNativeChartCoefficientMap (K := K) true (chartCoordinate I 3 0) =
      chartCoordinate L true false ^ 3 := by
  exact standardTwistedCubicChartThreeToLineChart_coordinate (K := K) 0

end PfaffianDescent.QuarticNet
