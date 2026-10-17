import PfaffianDescent.NativeOpenPullbackFramedSection
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentRefinedSectionCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealChartRefinement

/-! Ordinary bounded native framed coefficient transport. These generic inputs
are maps/frames; the original geometric callers derive them internally. -/
noncomputable section
namespace PfaffianDescent.BundleSectionZeroLocus
open AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Equality of original section maps implies equality of their whole native
pullback-frame coefficient, without unfolding the original coefficient module. -/
theorem nativePullbackFramedCoefficient_congr
    {X Y : Scheme.{u}} (j : Y ⟶ X) (T : X.Modules)
    (e : (Scheme.Modules.pullback j).obj T ≅ SheafOfModules.unit Y.ringCatSheaf)
    (s t : SheafOfModules.unit X.ringCatSheaf ⟶ T) (h : s = t) :
    unitEndomorphismValue
      (inv (I := isIso_pullbackUnitComparison j) (pullbackUnitComparison j) ≫
        (Scheme.Modules.pullback j).map s ≫ e.hom) =
    unitEndomorphismValue
      (inv (I := isIso_pullbackUnitComparison j) (pullbackUnitComparison j) ≫
        (Scheme.Modules.pullback j).map t ≫ e.hom) :=
  congrArg (fun a : SheafOfModules.unit X.ringCatSheaf ⟶ T =>
    unitEndomorphismValue
      (inv (I := isIso_pullbackUnitComparison j) (pullbackUnitComparison j) ≫
        (Scheme.Modules.pullback j).map a ≫ e.hom)) h

/-- Native open pullback-frame coefficient is the actual restriction-frame
coefficient, as an equality of original structure-sheaf sections. -/
theorem nativeOpenPullbackFramedCoefficient_eq_restricted
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] (T : X.Modules)
    (e : (Scheme.Modules.restrictFunctor j).obj T ≅ SheafOfModules.unit Y.ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T) :
    unitEndomorphismValue
      (inv (I := isIso_pullbackUnitComparison j) (pullbackUnitComparison j) ≫
        (Scheme.Modules.pullback j).map s ≫
        ((Scheme.Modules.restrictFunctorIsoPullback j).symm.app T ≪≫ e).hom) =
    unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso j).inv ≫
        (Scheme.Modules.restrictFunctor j).map s ≫ e.hom) :=
  congrArg unitEndomorphismValue
    (nativeOpenPullbackFramedSection_eq_restricted j T e s)

/-- Refining the original open frame gives the SAME literal pullback of
its old coefficient, for arbitrary actual module and section. -/
theorem nativeRefinedPullbackFramedCoefficient
    {X Y : Scheme.{u}} (U : X.Opens) (f : Y ⟶ (U : Scheme)) [IsOpenImmersion f]
    (T : X.Modules)
    (p : (Scheme.Modules.restrictFunctor U.ι).obj T ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ T) :
    unitEndomorphismValue
      (inv (I := isIso_pullbackUnitComparison (f ≫ U.ι))
        (pullbackUnitComparison (f ≫ U.ι)) ≫
        (Scheme.Modules.pullback (f ≫ U.ι)).map s ≫
        ((Scheme.Modules.restrictFunctorIsoPullback (f ≫ U.ι)).symm.app T ≪≫
          cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U f T p).hom) =
    f.appTop (unitEndomorphismValue
      ((Scheme.Modules.restrictUnitIso U.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map s ≫ p.hom)) := by
  have h := nativeOpenPullbackFramedCoefficient_eq_restricted (f ≫ U.ι) T
    (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U f T p) s
  exact h.trans (cubicClosedPointSerreSurfaceJetCotangent_refinedSectionCoefficient
    f U.ι T p s)

end PfaffianDescent.BundleSectionZeroLocus
