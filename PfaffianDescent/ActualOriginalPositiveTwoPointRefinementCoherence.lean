import PfaffianDescent.ActualPositiveTwistNativeRestrictionPullbackCoherence
import PfaffianDescent.ActualOriginalPositiveTwoPointContraction
import PfaffianDescent.ActualModulePointChartSourceFactorization

/- SOURCE ONLY / UNVERIFIED. Exact original O2 point trivialization is
its SAME source-factorization Iso followed by the internally computed
refined chart unit Iso. All original maps and factorization are retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualOriginalPositiveTwoPointRefinementCoherence
    {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp))
    (hP : (hypersurfaceToBase p hp).residueDegree P.1 = 4) :
    let C := actualOriginalQuarticCotangentChartChoice p hp P hP
    let I := equationIdeal p hp
    let ell : grading I 1 := ⟨coordinate I C.index, coordinate_mem I C.index⟩
    let U := Proj.basicOpen (grading I) (coordinate I C.index)
    let e := Proj.basicOpenIsoSpec (grading I) (coordinate I C.index)
      (coordinate_mem I C.index) (by decide : 0 < 1)
    let T := positiveSheafOfModules (grading I) 2
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let j := Spec.map (CommRingCat.ofHom C.residue)
    let r := cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv T
      (actualPositiveTwistChartUnitIso I ell 2)
    (actualModulePointChartSourceFactorizationIso (chartι I C.index) j q
      C.factorization T (SheafOfModules.unit
        (Spec (.of (ChartRing I C.index))).ringCatSheaf) r).hom ≫
        pullbackUnitComparison j =
      (actualOriginalPositiveTwoPointTrivialization p hp P hP).hom := by
  dsimp only
  let C := actualOriginalQuarticCotangentChartChoice p hp P hP
  let I := equationIdeal p hp
  let T := positiveSheafOfModules (grading I) 2
  let ell : grading I 1 := ⟨coordinate I C.index, coordinate_mem I C.index⟩
  let U := Proj.basicOpen (grading I) (coordinate I C.index)
  let e := Proj.basicOpenIsoSpec (grading I) (coordinate I C.index)
    (coordinate_mem I C.index) (by decide : 0 < 1)
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let j := Spec.map (CommRingCat.ofHom C.residue)
  let f := chartι I C.index
  let r := cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv T
    (actualPositiveTwistChartUnitIso I ell 2)
  let A := (Scheme.Modules.restrictFunctorIsoPullback f).inv.app T
  let Pj := Scheme.Modules.pullback j
  let v := (eqToIso (congrArg (fun q' => (Scheme.Modules.pullback q').obj T)
    C.factorization.symm)).hom
  let w := (Scheme.Modules.pullbackComp j f).inv.app T
  have h := congrArg (fun d => v ≫ w ≫ Pj.map d ≫ pullbackUnitComparison j)
    (actualPositiveTwistNativeRestrictionPullbackCoherence I C.index 2)
  change v ≫ w ≫ Pj.map A ≫ Pj.map r.hom ≫ pullbackUnitComparison j =
    v ≫ w ≫ Pj.map (actualPositiveTwistNativeChartUnitIso I C.index 2).hom ≫
      pullbackUnitComparison j
  simpa only [Functor.map_comp, Category.assoc] using h

end PfaffianDescent
