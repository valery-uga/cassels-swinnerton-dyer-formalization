import PfaffianDescent.ActualPositiveTwistChartUnit
import PfaffianDescent.BundleSectionZeroLocusNaturality

/- SOURCE ONLY / UNVERIFIED. The actually constructed positive-twist
chart trivialization sends its SAME homogeneous chart-basis map to the
actual unit, by inverse cancellation and genuine restriction naturality. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualPositiveTwistChartUnitIso_basis
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ) :
    (Scheme.Modules.restrictFunctor
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).map
      (actualPositiveTwistChartBasisInvHom I ell m) ≫
      (actualPositiveTwistChartUnitIso I ell m).hom =
    (Scheme.Modules.restrictUnitIso
      (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι).hom := by
  letI := actualPositiveTwistChartBasisInvHom_isIso I ell m
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  let R := Scheme.Modules.restrictFunctor U.ι
  change R.map (actualPositiveTwistChartBasisInvHom I ell m) ≫
    (inv (R.map (actualPositiveTwistChartBasisInvHom I ell m)) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom) = _
  rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualPositiveTwistChartPullbackUnitIso_basis
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ) :
    let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
    (Scheme.Modules.pullback U.ι).map (actualPositiveTwistChartBasisInvHom I ell m) ≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).inv.app
        (positiveSheafOfModules (grading I) m) ≫
      (actualPositiveTwistChartUnitIso I ell m).hom = pullbackUnitComparison U.ι := by
  dsimp only
  let f := (Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι
  let A := Scheme.Modules.restrictFunctorIsoPullback f
  rw [← Category.assoc, A.inv.naturality, Category.assoc,
    actualPositiveTwistChartUnitIso_basis]
  exact (pullbackUnitComparison_eq_restrict f).symm

end PfaffianDescent
