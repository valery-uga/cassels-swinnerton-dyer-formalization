import PfaffianDescent.NativeOriginalChartOverModuleEquivalence

/-! SOURCE ONLY. Installed original-chart naturality carries genuine native
framed actions to the same original over-site, without choosing new scalar maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] isIso_pullbackUnitComparison

/-- Same whole native framed scalar map, transported through the actual
original-image-open equivalence. -/
theorem nativeOriginalChartFramedScalarAction
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : j.opensRange = U) (M : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.pullback j).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (q : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (h : (Scheme.Modules.pullback j).map s ≫ e.hom = pullbackUnitComparison j ≫ q) :
    (nativeOriginalChartOverModuleEquivalence j U hU).functor.map (s.over U) ≫
      ((nativeOriginalChartOverPullbackComparison j U hU).app M ≪≫ e).hom =
    (nativeOriginalChartOverUnitIso j U hU).hom ≫ q := by
  change (nativeOriginalChartOverModuleEquivalence j U hU).functor.map (s.over U) ≫
      ((nativeOriginalChartOverPullbackComparison j U hU).app M).hom ≫ e.hom =
    ((nativeOriginalChartOverPullbackComparison j U hU).app
      (SheafOfModules.unit X.ringCatSheaf)).hom ≫ pullbackUnitComparison j ≫ q
  rw [← Category.assoc, nativeOriginalChartOverPullbackComparison_naturality,
    Category.assoc, h]

/-- Same coefficient-one basis map, transported to the actual original
image-open over-site by the genuine comparison. -/
theorem nativeOriginalChartFramedBasisAction
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : j.opensRange = U) (M : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.pullback j).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    (h : (Scheme.Modules.pullback j).map s ≫ e.hom = pullbackUnitComparison j) :
    (nativeOriginalChartOverModuleEquivalence j U hU).functor.map (s.over U) ≫
      ((nativeOriginalChartOverPullbackComparison j U hU).app M ≪≫ e).hom =
    (nativeOriginalChartOverUnitIso j U hU).hom := by
  have h' := nativeOriginalChartFramedScalarAction j U hU M s e (𝟙 _) (by
    simpa only [Category.comp_id] using h)
  simpa only [Category.comp_id] using h'

end PfaffianDescent
