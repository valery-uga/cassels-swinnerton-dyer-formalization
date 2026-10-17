import PfaffianDescent.VoisinStandardOpenExtVanishing
import PfaffianDescent.BundleSectionZeroLocus

/-! SOURCE ONLY. The original over-site on the image of an actual chart is
faithfully equivalent to modules on that actual chart; the comparison is to
SAME native pullback functor. No desired overlap equality is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] isIso_pullbackUnitComparison

private def nativeOriginalChartImageIso
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : j.opensRange = U) : Y ≅ (U : Scheme) :=
  IsOpenImmersion.isoOfRangeEq j U.ι (by
    rw [Scheme.Opens.range_ι]
    change (j.opensRange : Set X) = (U : Set X)
    exact congrArg (fun V : X.Opens => (V : Set X)) hU)

private theorem nativeOriginalChartImageIso_fac
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : j.opensRange = U) :
    (nativeOriginalChartImageIso j U hU).hom ≫ U.ι = j :=
  IsOpenImmersion.isoOfRangeEq_hom_fac j U.ι _

/-- GENUINE module equivalence from the original image-open over-site to
modules on the original chart, internally constructed from its proved image. -/
def nativeOriginalChartOverModuleEquivalence
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : j.opensRange = U) :
    SheafOfModules (X.ringCatSheaf.over U) ≌ Y.Modules :=
  (Scheme.Modules.overEquiv U).trans
    (schemeModulesEquivalenceOfIsoRestrict (nativeOriginalChartImageIso j U hU).symm)

/-- The equivalence's actual original-over restriction is the SAME
native pullback along the original chart, through installed comparisons. -/
def nativeOriginalChartOverPullbackComparison
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : j.opensRange = U) :
    SheafOfModules.overFunctor X.ringCatSheaf U ⋙
        (nativeOriginalChartOverModuleEquivalence j U hU).functor ≅
      Scheme.Modules.pullback j := by
  let H := SheafOfModules.overFunctor X.ringCatSheaf U
  let E := Scheme.Modules.overEquiv U
  let e := nativeOriginalChartImageIso j U hU
  let R := Scheme.Modules.restrictFunctor e.hom
  change H ⋙ (E.functor ⋙ R) ≅ Scheme.Modules.pullback j
  exact (Functor.associator H E.functor R).symm ≪≫
    Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U) R ≪≫
    (Scheme.Modules.restrictFunctorComp e.hom U.ι).symm ≪≫
    Scheme.Modules.restrictFunctorCongr (nativeOriginalChartImageIso_fac j U hU) ≪≫
    Scheme.Modules.restrictFunctorIsoPullback j

/-- Canonical actual unit comparison on the SAME chart-over equivalence. -/
def nativeOriginalChartOverUnitIso
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : j.opensRange = U) :
    (nativeOriginalChartOverModuleEquivalence j U hU).functor.obj
      ((SheafOfModules.unit X.ringCatSheaf).over U) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  (nativeOriginalChartOverPullbackComparison j U hU).app
    (SheafOfModules.unit X.ringCatSheaf) ≪≫ asIso (pullbackUnitComparison j)

/-- Entire original over-site morphisms have their SAME native chart map
under the actual comparison, including all original scalar actions. -/
theorem nativeOriginalChartOverPullbackComparison_naturality
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : j.opensRange = U)
    {M N : X.Modules} (f : M ⟶ N) :
    (nativeOriginalChartOverModuleEquivalence j U hU).functor.map (f.over U) ≫
        ((nativeOriginalChartOverPullbackComparison j U hU).app N).hom =
      ((nativeOriginalChartOverPullbackComparison j U hU).app M).hom ≫
        (Scheme.Modules.pullback j).map f := by
  change (SheafOfModules.overFunctor X.ringCatSheaf U ⋙
      (nativeOriginalChartOverModuleEquivalence j U hU).functor).map f ≫
      (nativeOriginalChartOverPullbackComparison j U hU).hom.app N =
    (nativeOriginalChartOverPullbackComparison j U hU).hom.app M ≫
      (Scheme.Modules.pullback j).map f
  exact (nativeOriginalChartOverPullbackComparison j U hU).hom.naturality f

/-- Chart equality detects equality of WHOLE original over-site morphisms.
The faithful functor is derived from the actual chart image, not supplied. -/
theorem nativeOriginalChartOverModuleEquivalence_map_eq_iff
    {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (U : X.Opens) (hU : j.opensRange = U)
    {M N : SheafOfModules (X.ringCatSheaf.over U)} (f g : M ⟶ N) :
    (nativeOriginalChartOverModuleEquivalence j U hU).functor.map f =
      (nativeOriginalChartOverModuleEquivalence j U hU).functor.map g ↔ f = g := by
  constructor
  · intro h
    exact (nativeOriginalChartOverModuleEquivalence j U hU).functor.map_injective h
  · intro h; exact congrArg (nativeOriginalChartOverModuleEquivalence j U hU).functor.map h

end PfaffianDescent
