import PfaffianDescent.NativeOpenChartBasisReflection
import PfaffianDescent.TwistedCubicPullbackCoordinateWholeChartAction
import PfaffianDescent.PositiveThreeNativePowerFrame

/-! SOURCE ONLY. Local comparison uses the ORIGINAL pulled coordinate maps
and ORIGINAL native power-frame maps, internally deriving basis invertibility.
No local frame, transition, rationality or global bundle certificate is input. -/
noncomputable section
set_option quotPrecheck false
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
local notation "M" => (Scheme.Modules.pullback
  (standardProjectiveLineToTwistedCubic (K := K))).obj (positiveSheafOfModules (grading I) 1)
local notation "N" => positiveSheafOfModules (grading L) 3

/-- Derive original-open invertibility from whole native basis action
BEFORE concrete projective charts or positive modules are substituted. -/
private theorem actualOriginalNativeChartBasisIsIsoCut
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : j.opensRange = U) {Q : X.Modules}
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ Q)
    (e : (Scheme.Modules.pullback j).obj Q ≅ SheafOfModules.unit Y.ringCatSheaf)
    (h : (Scheme.Modules.pullback j).map s ≫ e.hom = pullbackUnitComparison j) :
    IsIso (s.over U) := by
  letI : IsIso ((Scheme.Modules.pullback j).map s ≫ e.hom) := by
    rw [h]
    exact isIso_pullbackUnitComparison j
  letI : IsIso ((Scheme.Modules.pullback j).map s) :=
    IsIso.of_isIso_comp_right _ e.hom
  exact nativeOpenChart_overMap_isIso_of_pullbackMap_isIso j U hU s

/-- The original pulled selected-coordinate map is an actual basis on its
original basic open, derived internally from its SAME Spec-chart action. -/
theorem standardTwistedCubicPulledCoordinate_originalOpen_isIso (b : Bool) :
    IsIso ((standardTwistedCubicPulledCoordinateHom (K := K)
      (if b then 3 else 0)).over (quotientCoordinateOpen L b)) := by
  exact actualOriginalNativeChartBasisIsIsoCut (chartι L b)
    (quotientCoordinateOpen L b) (chartι_opensRange L b)
    (standardTwistedCubicPulledCoordinateHom (K := K) (if b then 3 else 0))
    (standardTwistedCubicPulledCoordinate_nativeChartUnitIso (K := K) b)
    (standardTwistedCubicPulledCoordinate_nativeChart_basis (K := K) b)

/-- Original native cubic-power basis on the SAME original basic open.
Degree-one generation is internally derived from the original Bool quotient. -/
theorem standardProjectiveLine_originalPowerFrame_over_isIso (b : Bool) :
    IsIso ((positiveThreePowerFrameHom (grading L)
      ⟨coordinate L b, coordinate_mem L b⟩).over (quotientCoordinateOpen L b)) := by
  let ell : grading L 1 := ⟨coordinate L b, coordinate_mem L b⟩
  have hspan : (HomogeneousIdeal.irrelevant (grading L)).toIdeal ≤
      Ideal.span (Set.range (fun f : grading L 1 => (f : CoordinateRing L))) :=
    gradedSurjective_irrelevant_le_span_degreeOne (homogeneousSubmodule Bool K) (grading L)
      (quotientGradedRingHom L) (quotientGradedRingHom_surjective L)
      mvPolynomial_irrelevant_le_span_degreeOne_small
  letI : IsIso ((Scheme.Modules.restrictFunctor (quotientCoordinateOpen L b).ι).map
      (positiveThreePowerFrameHom (grading L) ell)) :=
    positiveThreePowerFrameHom_restrict_isIso (grading L) ell hspan
  exact overFunctorMap_isIso_of_restrictMap_isIso (quotientCoordinateOpen L b)
    (positiveThreePowerFrameHom (grading L) ell)

/-- ACTUAL local comparison as inverse ORIGINAL source basis followed by
ORIGINAL target power basis. No unrelated trivialization is selected. -/
def standardTwistedCubicOriginalPowerBasisOverIso (b : Bool) :
    (M).over (quotientCoordinateOpen L b) ≅ (N).over (quotientCoordinateOpen L b) := by
  let s := standardTwistedCubicPulledCoordinateHom (K := K) (if b then 3 else 0)
  let t := positiveThreePowerFrameHom (grading L) ⟨coordinate L b, coordinate_mem L b⟩
  letI : IsIso (s.over (quotientCoordinateOpen L b)) :=
    standardTwistedCubicPulledCoordinate_originalOpen_isIso b
  letI : IsIso (t.over (quotientCoordinateOpen L b)) :=
    standardProjectiveLine_originalPowerFrame_over_isIso b
  exact (asIso (s.over (quotientCoordinateOpen L b))).symm ≪≫
    asIso (t.over (quotientCoordinateOpen L b))

end PfaffianDescent.QuarticNet
