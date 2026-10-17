import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal
import PfaffianDescent.CubicClosedPointSerreTensorStalkUnitIso

/-! SOURCE ONLY. Reuse existing native positive-twist chart frames for EVERY
polynomial variable type, transporting the actual basicOpen restriction to
its actual Spec(Away) chart. No new local freeness/Iso certificate is supplied. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist BundleSectionZeroLocus
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Canonical native chart pullback of an actual positive twist. The frame is
internally the existing positive homogeneous multiplication frame. The variable
index is arbitrary, so this covers both original P3 and the actual P1 model. -/
def positiveQuotientNativeChartPullbackUnitIso
    {K : Type u} {σ : Type} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K)) (j : σ) (m : ℕ) :
    (Scheme.Modules.pullback (chartι I j)).obj
      (positiveSheafOfModules (grading I) m) ≅
      SheafOfModules.unit (Spec (.of (ChartRing I j))).ringCatSheaf := by
  let U := quotientCoordinateOpen I j
  let e := Proj.basicOpenIsoSpec (grading I) (coordinate I j)
    (coordinate_mem I j) (by decide : 0 < 1)
  let M := positiveSheafOfModules (grading I) m
  let eU : (Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.unit (U : Scheme).ringCatSheaf :=
    (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫
      quotientCoordinatePositiveTwistUnitIso_all I j m
  letI : IsIso (pullbackUnitComparison e.inv) := isIso_pullbackUnitComparison e.inv
  let eUnit : (Scheme.Modules.pullback e.inv).obj
      (SheafOfModules.unit (U : Scheme).ringCatSheaf) ≅
      SheafOfModules.unit (Spec (.of (ChartRing I j))).ringCatSheaf :=
    asIso (pullbackUnitComparison e.inv)
  change (Scheme.Modules.pullback (e.inv ≫ U.ι)).obj M ≅ _
  exact (Scheme.Modules.pullbackComp e.inv U.ι).symm.app M ≪≫
    (Scheme.Modules.pullback e.inv).mapIso eU ≪≫ eUnit

/-- Transport a native chart frame along a PROVED original morphism square.
This ordinary functorial helper does not assert any global bundle Iso. -/
def pullbackChartUnitIso_of_actual_factorization
    {X Y T U : Scheme.{u}} (f : X ⟶ Y) (i : T ⟶ X)
    (a : T ⟶ U) (j : U ⟶ Y) (h : i ≫ f = a ≫ j)
    (M : Y.Modules)
    (e : (Scheme.Modules.pullback j).obj M ≅
      SheafOfModules.unit U.ringCatSheaf) :
    (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback f).obj M) ≅
      SheafOfModules.unit T.ringCatSheaf := by
  letI : IsIso (pullbackUnitComparison a) := isIso_pullbackUnitComparison a
  exact (Scheme.Modules.pullbackComp i f).app M ≪≫
    eqToIso (congrArg (fun g : T ⟶ Y => (Scheme.Modules.pullback g).obj M) h) ≪≫
    (Scheme.Modules.pullbackComp a j).symm.app M ≪≫
    (Scheme.Modules.pullback a).mapIso e ≪≫ asIso (pullbackUnitComparison a)

end PfaffianDescent
