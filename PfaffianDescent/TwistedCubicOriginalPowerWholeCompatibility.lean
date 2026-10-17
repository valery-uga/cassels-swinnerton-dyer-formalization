import PfaffianDescent.NativeOriginalChartFramedBasisAction
import PfaffianDescent.NativeOriginalBasisTransitionGluing
import PfaffianDescent.TwistedCubicOriginalPowerBasisComparison
import PfaffianDescent.ProjectiveLineOriginalPowerCubeChartAction

/-! SOURCE ONLY. Original selected coordinate maps and original native
power maps have the SAME whole transitions. The resulting actual local
comparison morphisms agree on EVERY original subopen of each overlap.
No transition, frame, compatibility or desired bundle certificate is input. -/
noncomputable section
set_option quotPrecheck false
namespace PfaffianDescent.QuarticNet
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open BundleSectionZeroLocus SchemeModuleInternalHom
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] isIso_pullbackUnitComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local notation "I" => standardTwistedCubicHomogeneousIdeal (K := K)
local notation "L" => (⊥ : HomogeneousIdeal (homogeneousSubmodule Bool K))
local notation "M" => (Scheme.Modules.pullback
  (standardProjectiveLineToTwistedCubic (K := K))).obj (positiveSheafOfModules (grading I) 1)
local notation "N" => positiveSheafOfModules (grading L) 3
local notation "s" => (fun b : Bool =>
  standardTwistedCubicPulledCoordinateHom (K := K) (if b then 3 else 0))
local notation "t" => (fun b : Bool => positiveThreePowerFrameHom (grading L)
  ⟨coordinate L b, coordinate_mem L b⟩)

/-- Actual original basis transitions coincide, derived from the original
parametrization's cubic coordinate-ratio actions on EACH original chart. -/
theorem standardTwistedCubicOriginalPower_wholeBasisTransition (b : Bool) :
    let U := quotientCoordinateOpen L b
    letI : IsIso ((s b).over U) := standardTwistedCubicPulledCoordinate_originalOpen_isIso b
    letI : IsIso ((t b).over U) := standardProjectiveLine_originalPowerFrame_over_isIso b
    (s (!b)).over U ≫ inv ((s b).over U) =
      (t (!b)).over U ≫ inv ((t b).over U) := by
  let U := quotientCoordinateOpen L b
  let j := chartι L b
  let E := nativeOriginalChartOverModuleEquivalence j U (chartι_opensRange L b)
  let n := nativeOriginalChartOverPullbackComparison j U (chartι_opensRange L b)
  let eM := n.app M ≪≫ standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) b
  let eN := n.app N ≪≫ standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b
  let w := nativeOriginalChartOverUnitIso j U (chartι_opensRange L b)
  let q := unitEndomorphismOfRegularFunction
    ((Scheme.ΓSpecIso (.of (ChartRing L b))).inv.hom (chartCoordinate L b (!b) ^ 3))
  letI : IsIso ((s b).over U) := standardTwistedCubicPulledCoordinate_originalOpen_isIso b
  letI : IsIso ((t b).over U) := standardProjectiveLine_originalPowerFrame_over_isIso b
  have hs : (Scheme.Modules.pullback j).map (s (!b)) ≫
      (standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) b).hom =
      pullbackUnitComparison j ≫ q := by
    cases b
    · exact standardTwistedCubicPulledCoordinate_false_other_action
    · exact standardTwistedCubicPulledCoordinate_true_other_action
  exact nativeOriginalBasisTransitions_eq_of_chartActions E
    ((s b).over U) ((s (!b)).over U) ((t b).over U) ((t (!b)).over U)
    eM eN w q
    (nativeOriginalChartFramedBasisAction j U (chartι_opensRange L b) M (s b)
      (standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) b)
      (standardTwistedCubicPulledCoordinate_nativeChart_basis b))
    (nativeOriginalChartFramedScalarAction j U (chartι_opensRange L b) M (s (!b))
      (standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) b) q hs)
    (nativeOriginalChartFramedBasisAction j U (chartι_opensRange L b) N (t b)
      (standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b)
      (standardProjectiveLineOriginalPower_nativeChart_basis b))
    (nativeOriginalChartFramedScalarAction j U (chartι_opensRange L b) N (t (!b))
      (standardProjectiveLineOriginalPower_nativeChartUnitIso (K := K) b) q
      (standardProjectiveLineOriginalPower_nativeChart_action b (!b)))

/-- The SAME actual local comparison carries the OTHER original selected
coordinate to the OTHER original cubic-power map. -/
theorem standardTwistedCubicOriginalPowerBasisOverIso_other (b : Bool) :
    (s (!b)).over (quotientCoordinateOpen L b) ≫
      (standardTwistedCubicOriginalPowerBasisOverIso (K := K) b).hom =
    (t (!b)).over (quotientCoordinateOpen L b) := by
  let U := quotientCoordinateOpen L b
  letI : IsIso ((s b).over U) := standardTwistedCubicPulledCoordinate_originalOpen_isIso b
  letI : IsIso ((t b).over U) := standardProjectiveLine_originalPowerFrame_over_isIso b
  change (s (!b)).over U ≫ inv ((s b).over U) ≫ (t b).over U = (t (!b)).over U
  exact nativeOriginalOtherBasis_comp_comparison ((s b).over U) ((s (!b)).over U)
    ((t b).over U) ((t (!b)).over U)
    (standardTwistedCubicOriginalPower_wholeBasisTransition b)

/-- SAME local comparison carries EACH original end coordinate to its
original target power map, as a whole original over-site morphism. -/
theorem standardTwistedCubicOriginalPowerBasisOverIso_end (b c : Bool) :
    (s c).over (quotientCoordinateOpen L b) ≫
      (standardTwistedCubicOriginalPowerBasisOverIso (K := K) b).hom =
    (t c).over (quotientCoordinateOpen L b) := by
  by_cases h : c = b
  · subst c
    let U := quotientCoordinateOpen L b
    letI : IsIso ((s b).over U) := standardTwistedCubicPulledCoordinate_originalOpen_isIso b
    letI : IsIso ((t b).over U) := standardProjectiveLine_originalPowerFrame_over_isIso b
    change (s b).over U ≫ inv ((s b).over U) ≫ (t b).over U = (t b).over U
    simp only [IsIso.hom_inv_id_assoc]
  · have hc : c = !b := by cases b <;> cases c <;> simp_all
    rw [hc]
    exact standardTwistedCubicOriginalPowerBasisOverIso_other b

/-- WHOLE overlap compatibility of the ACTUAL local comparison maps. It is
proved on ALL original overlap subopens using a genuine original basis. -/
theorem standardTwistedCubicOriginalPowerBasisOverIso_compatible (b c : Bool) :
    (SchemeModuleInternalHom.sheaf M N).val.map
        (homOfLE (show quotientCoordinateOpen L b ⊓ quotientCoordinateOpen L c ≤
          quotientCoordinateOpen L b from inf_le_left)).op
        ((sectionsEquivOver M N (quotientCoordinateOpen L b)).symm
          (standardTwistedCubicOriginalPowerBasisOverIso (K := K) b).hom) =
      (SchemeModuleInternalHom.sheaf M N).val.map
        (homOfLE (show quotientCoordinateOpen L b ⊓ quotientCoordinateOpen L c ≤
          quotientCoordinateOpen L c from inf_le_right)).op
        ((sectionsEquivOver M N (quotientCoordinateOpen L c)).symm
          (standardTwistedCubicOriginalPowerBasisOverIso (K := K) c).hom) := by
  letI : IsIso ((s c).over (quotientCoordinateOpen L c)) :=
    standardTwistedCubicPulledCoordinate_originalOpen_isIso c
  exact @nativeHomSections_compatible_of_commonOriginalBasis _ M N
    (quotientCoordinateOpen L b) (quotientCoordinateOpen L c) (s c) (t c)
    (standardTwistedCubicPulledCoordinate_originalOpen_isIso (K := K) c)
    (standardTwistedCubicOriginalPowerBasisOverIso (K := K) b).hom
    (standardTwistedCubicOriginalPowerBasisOverIso (K := K) c).hom
    (standardTwistedCubicOriginalPowerBasisOverIso_end b c)
    (standardTwistedCubicOriginalPowerBasisOverIso_end c c)

end PfaffianDescent.QuarticNet
