import PfaffianDescent.CorayOpenPullbackAdjunctionCoherence
import PfaffianDescent.CorayOwnGlobalConormalRankOne
import PfaffianDescent.RegularPrincipalImmersionNativeRankOne

/-!
Actual inverse-image rank-one charts and the literal pulled-back ideal
pairing. No pullback/dual comparison, dualizing property, perfectness,
cohomology finiteness or genus estimate is assumed or concluded.
SOURCE ONLY / UNVERIFIED. Root owns compiler and acceptance checks.
-/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Convert an actual over-site unit chart to the same open-scheme chart. -/
def schemeModuleRankOneRestrictUnitIso
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (Scheme.Modules.restrictFunctor U.ι).obj M ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e ≪≫
    (Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
    Scheme.Modules.restrictUnitIso U.ι

/-- The actual inverse-image chart of a genuine rank-one module is a
unit chart, using the accepted native open adjunction frame. -/
def schemeModulePullbackRankOneChartIso
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ (SheafOfModules.unit X.ringCatSheaf).over U) :
    (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj
      ((Scheme.Modules.pullback f).obj M) ≅
      SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
  schemeModuleOpenAdjunctionUnitFrameIso f U M
    (schemeModuleRankOneRestrictUnitIso M U e)

/-- Pullback preserves actual local rank one without global generators,
flatness or a supplied tensor-comparison isomorphism. -/
theorem schemeModuleLocallyRankOne_pullback
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (hM : schemeModuleLocallyRankOne M) :
    schemeModuleLocallyRankOne ((Scheme.Modules.pullback f).obj M) := by
  intro y
  obtain ⟨U, hy, ⟨e⟩⟩ := hM (f y)
  let V := f ⁻¹ᵁ U
  have hyV : y ∈ V := hy
  let eV := schemeModulePullbackRankOneChartIso f M U e
  exact ⟨V, hyV,
    ⟨ProjectiveNegativeTwist.overFunctorIsoUnit_of_restrictIsoUnit V eV⟩⟩

/-- On the OWN component, the actual pullback of its ambient ideal-dual
is rank one, internally from the genuine regular-principal ideal charts. -/
theorem RegularPrincipalImmersion.actualRestrictedIdealDual_locallyRankOne
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) :
    schemeModuleLocallyRankOne ((Scheme.Modules.pullback i).obj
      (SchemeModuleInternalHom.dual (IdealSheafDataModule.closedImmersionModule i))) :=
  schemeModuleLocallyRankOne_pullback i _
    (schemeModuleLocallyRankOne_dual _ H.inverseCartierTwist_locallyRankOne)

/-- The literal pullback of the OWN ideal evaluation followed by the
actual pullback-unit comparison is invertible. The source is P(I tensor
I-dual); it has NOT been replaced by P(I) tensor P(I-dual). -/
theorem RegularPrincipalImmersion.actualPulledBackIdealEvaluation_isIso
    {X Z : Scheme.{u}} {i : Z ⟶ X} [IsClosedImmersion i]
    (H : RegularPrincipalImmersion i) :
    IsIso ((Scheme.Modules.pullback i).map
        (SchemeModuleInternalHom.dualEvaluation
          (IdealSheafDataModule.closedImmersionModule i)) ≫
      BundleSectionZeroLocus.pullbackUnitComparison i) := by
  let M := IdealSheafDataModule.closedImmersionModule i
  obtain ⟨B, hB, ⟨eB⟩⟩ :=
    schemeModuleLocallyRankOne_pointwise_charts M H.inverseCartierTwist_locallyRankOne
  let hEval : IsIso (SchemeModuleInternalHom.dualEvaluation M) :=
    SchemeModuleInternalHom.dualEvaluation_isIso_of_pointwise_unitCharts M B hB eB
  let eEval : schemeModuleTensor M (SchemeModuleInternalHom.dual M) ≅
      SheafOfModules.unit X.ringCatSheaf :=
    @asIso _ _ _ _ (SchemeModuleInternalHom.dualEvaluation M) hEval
  let eUnit : (Scheme.Modules.pullback i).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Z.ringCatSheaf :=
    @asIso _ _ _ _ (BundleSectionZeroLocus.pullbackUnitComparison i)
      (BundleSectionZeroLocus.isIso_pullbackUnitComparison i)
  let e := (Scheme.Modules.pullback i).mapIso eEval ≪≫ eUnit
  change IsIso e.hom
  exact e.isIso_hom

end PfaffianDescent
end
