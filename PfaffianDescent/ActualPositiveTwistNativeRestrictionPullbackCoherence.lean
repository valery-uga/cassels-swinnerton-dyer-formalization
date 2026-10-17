import PfaffianDescent.ActualPositiveTwistRefinedChartBasisUnitAction
import PfaffianDescent.ActualPositiveTwistNativeChartBasisUnitAction

/- SOURCE ONLY / UNVERIFIED. Identify the ACTUAL refined restriction
unit Iso with the ACTUAL native pullback unit Iso by cancelling their
SAME internally proved invertible basis. No desired square premise. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

lemma actualPositiveTwistNativeRestrictionPullbackCoherence
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (a : Fin 4) (m : ℕ) :
    let ell : grading I 1 := ⟨coordinate I a, coordinate_mem I a⟩
    let U := Proj.basicOpen (grading I) (coordinate I a)
    let e := Proj.basicOpenIsoSpec (grading I) (coordinate I a)
      (coordinate_mem I a) (by decide : 0 < 1)
    let T := positiveSheafOfModules (grading I) m
    (Scheme.Modules.restrictFunctorIsoPullback (chartι I a)).inv.app T ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv T
        (actualPositiveTwistChartUnitIso I ell m)).hom =
      (actualPositiveTwistNativeChartUnitIso I a m).hom := by
  dsimp only
  let ell : grading I 1 := ⟨coordinate I a, coordinate_mem I a⟩
  let U := Proj.basicOpen (grading I) (coordinate I a)
  let e := Proj.basicOpenIsoSpec (grading I) (coordinate I a)
    (coordinate_mem I a) (by decide : 0 < 1)
  let T := positiveSheafOfModules (grading I) m
  let v := actualPositiveTwistChartBasisInvHom I ell m
  let A := Scheme.Modules.restrictFunctorIsoPullback (chartι I a)
  let B := Scheme.Modules.restrictFunctorComp e.inv U.ι
  letI := actualPositiveTwistChartBasisInvHom_isIso I ell m
  have hR : IsIso ((Scheme.Modules.restrictFunctor (chartι I a)).map v) := by
    apply (NatIso.isIso_map_iff B v).mpr
    change IsIso ((Scheme.Modules.restrictFunctor e.inv).map
      ((Scheme.Modules.restrictFunctor U.ι).map v))
    infer_instance
  letI := hR
  letI : IsIso ((Scheme.Modules.pullback (chartι I a)).map v) :=
    (NatIso.isIso_map_iff A v).mp hR
  apply (cancel_epi ((Scheme.Modules.pullback (chartι I a)).map v)).1
  rw [← Category.assoc, A.inv.naturality, Category.assoc,
    actualPositiveTwistRefinedChartUnitIso_basis]
  rw [← pullbackUnitComparison_eq_restrict]
  exact (actualPositiveTwistNativeChartUnitIso_basis I a m).symm

end PfaffianDescent
