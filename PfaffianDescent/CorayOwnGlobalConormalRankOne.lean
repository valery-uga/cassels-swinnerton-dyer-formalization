import PfaffianDescent.CorayOwnCartierConormalQuotientFree
import PfaffianDescent.SchemeModuleRankOneDualKernelIso
import PfaffianDescent.VoisinPositiveTwistTriviality
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
Actual global rank-one conormal and normal data on a regular-principal
closed immersion. The source chart cover is obtained from the defining
Cartesian squares; no source cover, conormal rank or normal pairing is input.
This is local-to-global normal-bundle data, not adjunction or a genus bound.
SOURCE ONLY / UNVERIFIED. Root owns all compiler and acceptance checks.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual source charts are open immersions by base change of the
actual target charts in the defining Cartesian squares. -/
theorem RegularPrincipalImmersion.actualSource_isOpenImmersion
    {X Z : Scheme.{u}} {i : Z ⟶ X}
    (H : RegularPrincipalImmersion i) (a : H.Index) :
    IsOpenImmersion (H.source a) := by
  letI : IsOpenImmersion (H.target a) := H.targetOpen a
  exact MorphismProperty.of_isPullback (H.cartesian a) inferInstance

/-- The same source charts cover the actual source scheme. This follows
from the target cover and existence of points in the actual pullback. -/
theorem RegularPrincipalImmersion.actualSource_covers
    {X Z : Scheme.{u}} {i : Z ⟶ X}
    (H : RegularPrincipalImmersion i) (x : Z) :
    ∃ a : H.Index, ∃ y : Spec (H.B a), H.source a y = x := by
  obtain ⟨a, y, hy⟩ := H.cover (i x)
  obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
    (H.cartesian a) y x hy
  exact ⟨a, z, hz⟩

/-- A genuine pullback unit chart along an open immersion gives a unit
chart on its actual open image, using only canonical scheme pullbacks. -/
def openImmersionPullbackUnitIsoOnRange
    {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    (M : Z.Modules)
    (e : (Scheme.Modules.pullback f).obj M ≅
      SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.restrictFunctor f.opensRange.ι).obj M ≅
      SheafOfModules.unit f.opensRange.toScheme.ringCatSheaf := by
  let j := f.isoOpensRange.inv
  letI : IsIso (BundleSectionZeroLocus.pullbackUnitComparison j) :=
    BundleSectionZeroLocus.isIso_pullbackUnitComparison j
  exact (Scheme.Modules.restrictFunctorIsoPullback f.opensRange.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr (Scheme.Hom.isoOpensRange_inv_comp f).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp j f).app M).symm ≪≫
    (Scheme.Modules.pullback j).mapIso e ≪≫
    asIso (BundleSectionZeroLocus.pullbackUnitComparison j)

/-- The OWN canonical conormal module is globally locally rank one,
internally from regular equations in its actual source charts. -/
theorem RegularPrincipalImmersion.actualConormal_locallyRankOne
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) :
    schemeModuleLocallyRankOne (actualClosedImmersionConormalModule i) := by
  intro x
  obtain ⟨a, y, hy⟩ := H.actualSource_covers x
  letI : IsOpenImmersion (H.source a) := H.actualSource_isOpenImmersion a
  let U := (H.source a).opensRange
  have hxU : x ∈ U := Scheme.Hom.mem_opensRange.mpr ⟨y, hy⟩
  let eU := openImmersionPullbackUnitIsoOnRange (H.source a)
    (actualClosedImmersionConormalModule i) (H.actualChartConormalUnitIso a)
  exact ⟨U, hxU,
    ⟨ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit U eU⟩⟩

/-- The OWN O-linear dual of the actual conormal is locally rank one.
No normal bundle or action is supplied by the caller. -/
theorem RegularPrincipalImmersion.actualNormal_locallyRankOne
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) :
    schemeModuleLocallyRankOne
      (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i)) :=
  schemeModuleLocallyRankOne_dual _ H.actualConormal_locallyRankOne

/-- Canonical conormal/normal evaluation on the same source scheme is
invertible, derived from the actual conormal unit neighborhoods. -/
theorem RegularPrincipalImmersion.actualConormalNormalEvaluation_isIso
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) :
    IsIso (SchemeModuleInternalHom.dualEvaluation
      (actualClosedImmersionConormalModule i)) := by
  classical
  obtain ⟨B, hB, ⟨eB⟩⟩ := schemeModuleLocallyRankOne_pointwise_charts
    (actualClosedImmersionConormalModule i) H.actualConormal_locallyRankOne
  exact SchemeModuleInternalHom.dualEvaluation_isIso_of_pointwise_unitCharts
    (actualClosedImmersionConormalModule i) B hB eB

end PfaffianDescent
end
