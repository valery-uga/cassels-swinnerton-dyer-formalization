import PfaffianDescent.NativePullbackFrameFactorAction
import PfaffianDescent.TwistedCubicNativeChartPullbackScalar
import PfaffianDescent.TwistedCubicNativeCanonicalFrameCoefficient

/-! SOURCE ONLY. The SAME original parametrization pulls the original
coordinate sections to entire native maps whose genuine chart action is
internally derived. No transition or global bundle Iso is supplied. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] isIso_pullbackUnitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))
local notation "v" => standardProjectiveLineToTwistedCubic (K := K)
local notation "T" => positiveSheafOfModules (grading I) 1

/-- The SAME pulled section constructor, before concrete projective schemes
and positive modules are substituted. The inverse witness is explicit. -/
private def actualPulledCoordinateHomFactory
    {X Y : Scheme.{u}} (f : X ⟶ Y) (Q : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ Q) :
    SheafOfModules.unit X.ringCatSheaf ⟶ (Scheme.Modules.pullback f).obj Q :=
  CategoryTheory.inv («I» := isIso_pullbackUnitComparison f)
    (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map s

/-- The SAME factorization frame constructor at abstract scheme/module level. -/
private def actualPulledCoordinateNativeChartFactory
    {X Y W V : Scheme.{u}} (f : X ⟶ Y) (i : W ⟶ X)
    (a : W ⟶ V) (j : V ⟶ Y) (h : i ≫ f = a ≫ j) (Q : Y.Modules)
    (e : (Scheme.Modules.pullback j).obj Q ≅ SheafOfModules.unit V.ringCatSheaf) :
    (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback f).obj Q) ≅
      SheafOfModules.unit W.ringCatSheaf :=
  pullbackChartUnitIso_of_actual_factorization f i a j h Q e

/-- Actual pulled original coordinate-section morphism on the original P1. -/
def standardTwistedCubicPulledCoordinateHom (k : Fin 4) :
    SheafOfModules.unit (scheme L).ringCatSheaf ⟶ (Scheme.Modules.pullback v).obj T :=
  actualPulledCoordinateHomFactory v T
    (standardTwistedCubicPositiveOneCoordinateHom (K := K) k)

/-- Canonical native source frame on an ORIGINAL line chart, through its
PROVED original cubic-chart square. -/
def standardTwistedCubicPulledCoordinate_nativeChartUnitIso (b : Bool) :
    (Scheme.Modules.pullback (chartι L b)).obj ((Scheme.Modules.pullback v).obj T) ≅
      SheafOfModules.unit (Spec (.of (ChartRing L b))).ringCatSheaf :=
  actualPulledCoordinateNativeChartFactory v (chartι L b)
    (standardTwistedCubicNativeChartMorphism (K := K) b) (chartι I (if b then 3 else 0))
    (standardTwistedCubicNativeChartMorphism_toCurve b).symm T
    (standardTwistedCubicPositiveOne_canonicalNativeChartUnitIso (if b then 3 else 0))

/-- Cancel a unit inverse before ANY geometric substitution. -/
private theorem wholeUnitScalar_cancelInverseCut
    {C : Type*} [Category C] {A B : C} (c : A ⟶ B) [IsIso c]
    (m : A ⟶ B) (z : B ⟶ B) (h : inv c ≫ m = z) : m = c ≫ z :=
  (IsIso.inv_comp_eq c).mp h

/-- Original canonical whole scalar, with inverse cancellation bounded by
an abstract categorical theorem rather than rewriting a concrete chart alias. -/
private theorem originalCanonicalChartWholeActionCut (j k : Fin 4) :
    (Scheme.Modules.pullback (chartι I j)).map
        (standardTwistedCubicPositiveOneCoordinateHom (K := K) k) ≫
      (standardTwistedCubicPositiveOne_canonicalNativeChartUnitIso (K := K) j).hom =
    pullbackUnitComparison (chartι I j) ≫ unitEndomorphismOfRegularFunction
      ((Scheme.ΓSpecIso (.of (ChartRing I j))).inv.hom (chartCoordinate I j k)) := by
  letI : IsIso (pullbackUnitComparison (chartι I j)) :=
    isIso_pullbackUnitComparison (chartι I j)
  exact wholeUnitScalar_cancelInverseCut (pullbackUnitComparison (chartι I j)) _ _
    (standardTwistedCubicPositiveOne_canonicalNativeChart_unitScalar (K := K) j k)

/-- Bound the entire action conversion before the original concrete
parametrization, charts, section or canonical native frame are substituted. -/
private theorem actualPulledCoordinateNativeChartFactory_action
    {X Y W V : Scheme.{u}} (f : X ⟶ Y) (i : W ⟶ X)
    (a : W ⟶ V) [IsOpenImmersion a] (j : V ⟶ Y)
    (h : i ≫ f = a ≫ j) (Q : Y.Modules)
    (e : (Scheme.Modules.pullback j).obj Q ≅ SheafOfModules.unit V.ringCatSheaf)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ Q) (r : Γ(V, ⊤))
    (hs : (Scheme.Modules.pullback j).map s ≫ e.hom =
      pullbackUnitComparison j ≫ unitEndomorphismOfRegularFunction r) :
    (Scheme.Modules.pullback i).map (actualPulledCoordinateHomFactory f Q s) ≫
      (actualPulledCoordinateNativeChartFactory f i a j h Q e).hom =
    pullbackUnitComparison i ≫ unitEndomorphismOfRegularFunction (a.appTop.hom r) := by
  exact pullbackChartUnitIso_of_actual_factorization_scalarAction f i a j h Q e s r hs

/-- Scalar congruence at abstract scheme level, avoiding rewrites through
concrete module-sheaf types in the end-ratio consumers. -/
private theorem wholeChartScalar_congrCut {W : Scheme.{u}}
    {P : W.Modules} (c : P ⟶ SheafOfModules.unit W.ringCatSheaf)
    {r t : Γ(W, ⊤)} (h : r = t) :
    c ≫ unitEndomorphismOfRegularFunction r = c ≫ unitEndomorphismOfRegularFunction t :=
  congrArg (fun z => c ≫ unitEndomorphismOfRegularFunction z) h

/-- Unit scalar action simplified before ANY original chart substitution. -/
private theorem wholeChartScalar_oneCut {W : Scheme.{u}}
    {P : W.Modules} (c : P ⟶ SheafOfModules.unit W.ringCatSheaf) :
    c ≫ unitEndomorphismOfRegularFunction (1 : Γ(W, ⊤)) = c := by
  rw [unitEndomorphismOfRegularFunction_one]
  exact Category.comp_id c

/-- Self-coordinate scalar calculation independent of all positive modules
and native frame constructors. -/
private theorem originalNativeChart_selfScalarCut (b : Bool) :
    (standardTwistedCubicNativeChartMorphism (K := K) b).appTop.hom
      ((Scheme.ΓSpecIso (.of (ChartRing I (if b then 3 else 0)))).inv.hom
        (chartCoordinate I (if b then 3 else 0) (if b then 3 else 0))) = 1 := by
  rw [chartCoordinate_self, map_one, map_one]

/-- WHOLE chart action of EVERY original pulled homogeneous coordinate.
It is derived from the native coefficient and the actual chart square. -/
theorem standardTwistedCubicPulledCoordinate_nativeChart_action (b : Bool) (k : Fin 4) :
    (Scheme.Modules.pullback (chartι L b)).map
        (standardTwistedCubicPulledCoordinateHom (K := K) k) ≫
      (standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) b).hom =
    pullbackUnitComparison (chartι L b) ≫
      unitEndomorphismOfRegularFunction
        ((standardTwistedCubicNativeChartMorphism (K := K) b).appTop.hom
          ((Scheme.ΓSpecIso (.of (ChartRing I (if b then 3 else 0)))).inv.hom
            (chartCoordinate I (if b then 3 else 0) k))) := by
  letI : IsOpenImmersion (standardTwistedCubicNativeChartMorphism (K := K) b) :=
    standardTwistedCubicNativeChartMorphism_isOpenImmersion b
  exact actualPulledCoordinateNativeChartFactory_action v (chartι L b)
    (standardTwistedCubicNativeChartMorphism (K := K) b) (chartι I (if b then 3 else 0))
    (standardTwistedCubicNativeChartMorphism_toCurve b).symm T
    (standardTwistedCubicPositiveOne_canonicalNativeChartUnitIso (K := K) (if b then 3 else 0))
    (standardTwistedCubicPositiveOneCoordinateHom (K := K) k)
    ((Scheme.ΓSpecIso (.of (ChartRing I (if b then 3 else 0)))).inv.hom
      (chartCoordinate I (if b then 3 else 0) k))
    (originalCanonicalChartWholeActionCut (if b then 3 else 0) k)

/-- The pulled OTHER end frame on the first original chart acts by the
actual cube of its native line ratio, as an entire module morphism. -/
theorem standardTwistedCubicPulledCoordinate_false_other_action :
    (Scheme.Modules.pullback (chartι L false)).map
        (standardTwistedCubicPulledCoordinateHom (K := K) 3) ≫
      (standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) false).hom =
    pullbackUnitComparison (chartι L false) ≫
      unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso (.of (ChartRing L false))).inv.hom
          (chartCoordinate L false true ^ 3)) := by
  exact (standardTwistedCubicPulledCoordinate_nativeChart_action (K := K) false 3).trans
    (wholeChartScalar_congrCut (pullbackUnitComparison (chartι L false))
      (standardTwistedCubicNativeChartMorphism_false_appTop_endRatio (K := K)))

/-- The pulled OTHER end frame on the last original chart acts by the
actual cube of the reciprocal ratio, as an entire module morphism. -/
theorem standardTwistedCubicPulledCoordinate_true_other_action :
    (Scheme.Modules.pullback (chartι L true)).map
        (standardTwistedCubicPulledCoordinateHom (K := K) 0) ≫
      (standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) true).hom =
    pullbackUnitComparison (chartι L true) ≫
      unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso (.of (ChartRing L true))).inv.hom
          (chartCoordinate L true false ^ 3)) := by
  exact (standardTwistedCubicPulledCoordinate_nativeChart_action (K := K) true 0).trans
    (wholeChartScalar_congrCut (pullbackUnitComparison (chartι L true))
      (standardTwistedCubicNativeChartMorphism_true_appTop_endRatio (K := K)))

/-- The ORIGINAL selected pulled end coordinate is a genuine native basis
on EACH original line chart, internally derived rather than assumed. -/
theorem standardTwistedCubicPulledCoordinate_nativeChart_basis (b : Bool) :
    (Scheme.Modules.pullback (chartι L b)).map
        (standardTwistedCubicPulledCoordinateHom (K := K) (if b then 3 else 0)) ≫
      (standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) b).hom =
    pullbackUnitComparison (chartι L b) := by
  exact (standardTwistedCubicPulledCoordinate_nativeChart_action (K := K) b
    (if b then 3 else 0)).trans
      ((wholeChartScalar_congrCut (pullbackUnitComparison (chartι L b))
        (originalNativeChart_selfScalarCut (K := K) b)).trans
        (wholeChartScalar_oneCut (pullbackUnitComparison (chartι L b))))

end PfaffianDescent.QuarticNet
