import PfaffianDescent.NativeAwayCubicPowerRatio
import PfaffianDescent.PositiveThreeNativeRefinedCoefficient
import PfaffianDescent.QuarticTwistedCubicProjectiveLine

/-! SOURCE ONLY. WHOLE native cubic-power chart action on the ORIGINAL
Bool quotient projective line. No transition or coefficient certificate is input. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] isIso_pullbackUnitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))

private lemma originalLineDegreeOneGeneration :
    (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤
      Ideal.span (Set.range (fun f : grading L 1 => (f : CoordinateRing L))) :=
  gradedSurjective_irrelevant_le_span_degreeOne (homogeneousSubmodule Bool K) (grading L)
    (quotientGradedRingHom L) (quotientGradedRingHom_surjective L)
    mvPolynomial_irrelevant_le_span_degreeOne_small

/-- Degree-one generation for an ABSTRACT original Bool quotient. -/
private lemma quotientLineDegreeOneGeneration
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) :
    (HomogeneousIdeal.irrelevant (grading J)).toIdeal ≤
      Ideal.span (Set.range (fun f : grading J 1 => (f : CoordinateRing J))) :=
  gradedSurjective_irrelevant_le_span_degreeOne (homogeneousSubmodule Bool K) (grading J)
    (quotientGradedRingHom J) (quotientGradedRingHom_surjective J)
    mvPolynomial_irrelevant_le_span_degreeOne_small

/-- The IDENTICAL native frame constructor, kept behind an abstract
ideal-indexed factory before the original bottom quotient is substituted. -/
private def quotientLineNativePowerChartUnitIso
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b : Bool) :
    (Scheme.Modules.pullback (chartι J b)).obj (positiveSheafOfModules (grading J) 3) ≅
      SheafOfModules.unit (Spec (.of (ChartRing J b))).ringCatSheaf :=
  positiveThreePowerFrame_nativeChartUnitIso (grading J)
    ⟨coordinate J b, coordinate_mem J b⟩ (quotientLineDegreeOneGeneration J)

/-- Actual native chart frame of the ORIGINAL cubic-power map. -/
def standardProjectiveLineOriginalPower_nativeChartUnitIso (b : Bool) :
    (Scheme.Modules.pullback (chartι L b)).obj (positiveSheafOfModules (grading L) 3) ≅
      SheafOfModules.unit (Spec (.of (ChartRing L b))).ringCatSheaf :=
  quotientLineNativePowerChartUnitIso L b

/-- Bounded cancellation and fraction rewrite in the SAME generic grading,
before any original Bool quotient, scheme or native frame is substituted. -/
private theorem nativeCubicPowerChartActionCut
    {A ρ : Type u} [CommRing A] [SetLike ρ A] [AddSubgroupClass ρ A]
    (G : ℕ → ρ) [GradedRing G] (ell eta : G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤
      Ideal.span (Set.range (fun f : G 1 => (f : A)))) :
    (Scheme.Modules.pullback (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)).map
        (positiveThreePowerFrameHom G eta) ≫
      (positiveThreePowerFrame_nativeChartUnitIso G ell hspan).hom =
    pullbackUnitComparison (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one) ≫
      unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso (.of (Away G (ell : A)))).inv.hom
          ((Away.mk G ell.property 1 (eta : A) (by simpa using eta.property)) ^ 3)) := by
  let c := pullbackUnitComparison (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)
  letI : IsIso c := isIso_pullbackUnitComparison
    (Proj.awayι G (ell : A) ell.property Nat.zero_lt_one)
  have h := positiveThreePowerFrame_nativeChart_coordinateUnitScalar G ell eta hspan
  rw [nativeAway_degreeOnePower_cubicRatio G ell eta] at h
  exact (IsIso.inv_comp_eq c).mp h

/-- Isolate only the actual pullback-map alias, before composition. -/
private theorem quotientLineNativePowerMap_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b c : Bool) :
    (Scheme.Modules.pullback (chartι J b)).map
      (positiveThreePowerFrameHom (grading J) ⟨coordinate J c, coordinate_mem J c⟩) =
    (Scheme.Modules.pullback (Proj.awayι (grading J) (coordinate J b)
      (coordinate_mem J b) Nat.zero_lt_one)).map
      (positiveThreePowerFrameHom (grading J) ⟨coordinate J c, coordinate_mem J c⟩) := rfl

/-- Isolate only the original frame morphism and its identical raw constructor. -/
private theorem quotientLineNativeFrameHom_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b : Bool) :
    (quotientLineNativePowerChartUnitIso J b).hom =
    (positiveThreePowerFrame_nativeChartUnitIso (grading J)
      ⟨coordinate J b, coordinate_mem J b⟩ (quotientLineDegreeOneGeneration J)).hom := rfl

/-- The left-hand action is transported by the two individual map/frame
identities; the coefficient/unit comparison side is not unfolded here. -/
private theorem quotientLineNativePowerLeft_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b c : Bool) :
    (Scheme.Modules.pullback (chartι J b)).map
        (positiveThreePowerFrameHom (grading J) ⟨coordinate J c, coordinate_mem J c⟩) ≫
      (quotientLineNativePowerChartUnitIso J b).hom =
    (Scheme.Modules.pullback (Proj.awayι (grading J) (coordinate J b)
        (coordinate_mem J b) Nat.zero_lt_one)).map
        (positiveThreePowerFrameHom (grading J) ⟨coordinate J c, coordinate_mem J c⟩) ≫
      (positiveThreePowerFrame_nativeChartUnitIso (grading J)
        ⟨coordinate J b, coordinate_mem J b⟩ (quotientLineDegreeOneGeneration J)).hom := by
  rw [quotientLineNativePowerMap_eq_raw, quotientLineNativeFrameHom_eq_raw]

/-- Isolate only the actual canonical unit-comparison morphism alias. -/
private theorem quotientLineNativeUnitComparison_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b : Bool) :
    pullbackUnitComparison (chartι J b) =
      pullbackUnitComparison (Proj.awayι (grading J) (coordinate J b)
        (coordinate_mem J b) Nat.zero_lt_one) := rfl

/-- Isolate only the literal structure-sheaf scalar/normalized fraction alias. -/
private theorem quotientLineNativePowerScalar_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b c : Bool) :
    unitEndomorphismOfRegularFunction
      ((Scheme.ΓSpecIso (.of (ChartRing J b))).inv.hom (chartCoordinate J b c ^ 3)) =
    unitEndomorphismOfRegularFunction
      ((Scheme.ΓSpecIso (.of (Away (grading J) (coordinate J b)))).inv.hom
        ((Away.mk (grading J) (coordinate_mem J b) 1 (coordinate J c)
          (by simpa using coordinate_mem J c)) ^ 3)) := rfl

/-- The right-hand action is transported independently of any positive
module, homogeneous-section map or native frame definition. -/
private theorem quotientLineNativePowerRight_eq_raw
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b c : Bool) :
    pullbackUnitComparison (chartι J b) ≫
      unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso (.of (ChartRing J b))).inv.hom (chartCoordinate J b c ^ 3)) =
    pullbackUnitComparison (Proj.awayι (grading J) (coordinate J b)
        (coordinate_mem J b) Nat.zero_lt_one) ≫
      unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso (.of (Away (grading J) (coordinate J b)))).inv.hom
          ((Away.mk (grading J) (coordinate_mem J b) 1 (coordinate J c)
            (by simpa using coordinate_mem J c)) ^ 3)) := by
  rw [quotientLineNativeUnitComparison_eq_raw, quotientLineNativePowerScalar_eq_raw]

/-- Alias normalization at the ABSTRACT ideal level: the theorem uses
the same original chartι/ChartRing-shaped header and the shared frame factory. -/
private theorem quotientLineNativeCubicPowerChartAction
    (J : HomogeneousIdeal (homogeneousSubmodule Bool K)) (b c : Bool) :
    (Scheme.Modules.pullback (chartι J b)).map
        (positiveThreePowerFrameHom (grading J) ⟨coordinate J c, coordinate_mem J c⟩) ≫
      (quotientLineNativePowerChartUnitIso J b).hom =
    pullbackUnitComparison (chartι J b) ≫
      unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso (.of (ChartRing J b))).inv.hom (chartCoordinate J b c ^ 3)) := by
  calc
    _ = _ := quotientLineNativePowerLeft_eq_raw J b c
    _ = _ := nativeCubicPowerChartActionCut (grading J)
      ⟨coordinate J b, coordinate_mem J b⟩
      ⟨coordinate J c, coordinate_mem J c⟩ (quotientLineDegreeOneGeneration J)
    _ = _ := (quotientLineNativePowerRight_eq_raw J b c).symm

/-- The shared factory preserves the ORIGINAL frame definitionally;
only degree-one-generation proof witnesses differ, by proof irrelevance. -/
private theorem originalPowerNativeFrame_factory_preserves (b : Bool) :
    standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b =
      positiveThreePowerFrame_nativeChartUnitIso (grading L)
        ⟨coordinate L b, coordinate_mem L b⟩
        (originalLineDegreeOneGeneration (K := K)) := rfl

/-- Specialize the already bounded generic action on its RAW original
graded away chart, before expanding the original ChartRing/chartι/frame aliases. -/
private theorem originalRawNativeCubicPowerChartAction (b c : Bool) :
    (Scheme.Modules.pullback (Proj.awayι (grading L) (coordinate L b)
      (coordinate_mem L b) Nat.zero_lt_one)).map
        (positiveThreePowerFrameHom (grading L) ⟨coordinate L c, coordinate_mem L c⟩) ≫
      (positiveThreePowerFrame_nativeChartUnitIso (grading L)
        ⟨coordinate L b, coordinate_mem L b⟩
        (originalLineDegreeOneGeneration (K := K))).hom =
    pullbackUnitComparison (Proj.awayι (grading L) (coordinate L b)
      (coordinate_mem L b) Nat.zero_lt_one) ≫
      unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso (.of (Away (grading L) (coordinate L b)))).inv.hom
          ((Away.mk (grading L) (coordinate_mem L b) 1 (coordinate L c)
            (by simpa using coordinate_mem L c)) ^ 3)) :=
  nativeCubicPowerChartActionCut (grading L)
    ⟨coordinate L b, coordinate_mem L b⟩
    ⟨coordinate L c, coordinate_mem L c⟩
    (originalLineDegreeOneGeneration (K := K))

/-- Normalize only the fraction, independently of the scheme-module maps. -/
private theorem originalRawNativeCubicPowerChartRatio (b c : Bool) :
    (Away.mk (grading L) (coordinate_mem L b) 1 (coordinate L c)
      (by simpa using coordinate_mem L c)) ^ 3 = chartCoordinate L b c ^ 3 := rfl

/-- Concrete original-to-factory transport of ONLY the frame morphism,
before it is composed with a pulled section or scalar action. -/
private theorem originalNativePowerFrameHom_eq_factory (b : Bool) :
    (standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b).hom =
      (quotientLineNativePowerChartUnitIso (K := K) L b).hom := rfl

/-- WHOLE chart action of EACH original native power map: multiplication
by the actual cube of the SAME original line coordinate ratio. -/
theorem standardProjectiveLineOriginalPower_nativeChart_action (b c : Bool) :
    (Scheme.Modules.pullback (chartι L b)).map
        (positiveThreePowerFrameHom (grading L) ⟨coordinate L c, coordinate_mem L c⟩) ≫
      (standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b).hom =
    pullbackUnitComparison (chartι L b) ≫
      unitEndomorphismOfRegularFunction
        ((Scheme.ΓSpecIso (.of (ChartRing L b))).inv.hom (chartCoordinate L b c ^ 3)) := by
  have hFrame := originalNativePowerFrameHom_eq_factory (K := K) b
  have hAction := quotientLineNativeCubicPowerChartAction (K := K) L b c
  calc
    _ = (Scheme.Modules.pullback (chartι L b)).map
        (positiveThreePowerFrameHom (grading L) ⟨coordinate L c, coordinate_mem L c⟩) ≫
        (quotientLineNativePowerChartUnitIso (K := K) L b).hom :=
      congrArg (fun e => (Scheme.Modules.pullback (chartι L b)).map
        (positiveThreePowerFrameHom (grading L) ⟨coordinate L c, coordinate_mem L c⟩) ≫ e) hFrame
    _ = _ := hAction

/-- Selected original power map is a genuine coefficient-one native basis. -/
theorem standardProjectiveLineOriginalPower_nativeChart_basis (b : Bool) :
    (Scheme.Modules.pullback (chartι L b)).map
        (positiveThreePowerFrameHom (grading L) ⟨coordinate L b, coordinate_mem L b⟩) ≫
      (standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b).hom =
    pullbackUnitComparison (chartι L b) := by
  rw [standardProjectiveLineOriginalPower_nativeChart_action,
    chartCoordinate_self, one_pow, map_one, unitEndomorphismOfRegularFunction_one,
    Category.comp_id]

end PfaffianDescent.QuarticNet
