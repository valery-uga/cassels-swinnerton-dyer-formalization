import PfaffianDescent.ActualOneVariableAffineDifferentialFrame
import PfaffianDescent.LineGrassmannianProjCharts
import PfaffianDescent.ActualOpenImmersionDifferentialSheafIso
import PfaffianDescent.BundleSectionZeroLocus

/- SOURCE ONLY / UNVERIFIED. Native differential frames on an ACTUAL covering
atlas of the SAME projectiveLineProj K, retaining its ORIGINAL base map. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [CommRing K]
local notation "Iline" => (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule Bool K))

/-- Only a presentation of the ORIGINAL P1 affine chart ring is changed. -/
def actualProjectiveLinePolynomialChartIso (b : Bool) :
    Spec (.of (MvPolynomial {i : Bool // i ≠ b} K)) ≅
      Spec (.of (ChartRing Iline b)) :=
  Scheme.Spec.mapIso (chartPolynomialEquiv (R := K) b).symm.toCommRingCatIso.op

/-- Actual polynomial presentation followed by the ORIGINAL coordinate chart
immersion into projectiveLineProj K. -/
def actualProjectiveLinePolynomialChartToLine (b : Bool) :
    Spec (.of (MvPolynomial {i : Bool // i ≠ b} K)) ⟶ projectiveLineProj K :=
  (actualProjectiveLinePolynomialChartIso K b).hom ≫ chartι Iline b

instance actualProjectiveLinePolynomialChartToLine_isOpenImmersion (b : Bool) :
    IsOpenImmersion (actualProjectiveLinePolynomialChartToLine K b) := by
  dsimp only [actualProjectiveLinePolynomialChartToLine]
  infer_instance

/-- The chart map has exactly its ORIGINAL coefficient structure map. -/
theorem actualProjectiveLinePolynomialChartToLine_toBase (b : Bool) :
    actualProjectiveLinePolynomialChartToLine K b ≫ projectiveLineProjToBase K =
      Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial {i : Bool // i ≠ b} K))) := by
  let e := chartPolynomialEquiv (R := K) b
  change (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ chartι Iline b) ≫
    toBase Iline = Spec.map (CommRingCat.ofHom MvPolynomial.C)
  rw [Category.assoc, chartι_toBase, ← Spec.map_comp]
  apply congrArg (fun p : K →+* MvPolynomial {i : Bool // i ≠ b} K =>
    Spec.map (CommRingCat.ofHom p))
  apply RingHom.ext
  intro r
  change e.symm (chartBaseMap Iline b r) = MvPolynomial.C r
  rw [← chartPolynomialEquiv_C (R := K) b r]
  exact e.symm_apply_apply _

/-- The ACTUAL pullback of original P1 relative Omega is trivial on each
original polynomial chart. Every frame and base equality is produced internally. -/
def actualProjectiveLinePolynomialChartDifferentialFrameIso (b : Bool) :
    (Scheme.Modules.pullback (actualProjectiveLinePolynomialChartToLine K b)).obj
        (schemeRelativeDifferentials (projectiveLineProjToBase K)) ≅
      SheafOfModules.unit
        (Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))).ringCatSheaf := by
  letI : Subsingleton {i : Bool // i ≠ b} :=
    (lineProjectiveVariableEquiv b).symm.subsingleton
  let a : {i : Bool // i ≠ b} := lineProjectiveVariableEquiv b (0, 0)
  let f := actualProjectiveLinePolynomialChartToLine K b
  let g := projectiveLineProjToBase K
  let hbase := actualProjectiveLinePolynomialChartToLine_toBase K b
  exact (actualOpenImmersionDifferentialSheafPullbackIso f g).symm ≪≫
    eqToIso (congrArg (fun h => schemeRelativeDifferentials h) hbase) ≪≫
    actualOneVariableAffineDifferentialFrameIso (K := K) a

/-- The two actual framed chart maps cover EVERY point of ORIGINAL P1. -/
theorem exists_actualProjectiveLinePolynomialChart (x : projectiveLineProj K) :
    ∃ (b : Bool) (y : Spec (.of (MvPolynomial {i : Bool // i ≠ b} K))),
      actualProjectiveLinePolynomialChartToLine K b y = x := by
  obtain ⟨b, y, hy⟩ := exists_coordinate_chart Iline x
  let e := actualProjectiveLinePolynomialChartIso K b
  refine ⟨b, e.inv y, ?_⟩
  have he : e.hom (e.inv y) = y :=
    congrArg (fun f : Spec (.of (ChartRing Iline b)) ⟶
      Spec (.of (ChartRing Iline b)) => f y) e.inv_hom_id
  change chartι Iline b (e.hom (e.inv y)) = x
  rw [he]
  exact hy

end PfaffianDescent
end
