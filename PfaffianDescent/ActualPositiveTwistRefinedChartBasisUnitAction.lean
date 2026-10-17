import PfaffianDescent.ActualPositiveTwistChartBasisUnitAction
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentRefinedSectionCoefficient
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentIdealChartRefinement

/- SOURCE ONLY / UNVERIFIED. The SAME actual basis has unit coefficient
under genuine native restriction/chart refinement, with no comparison
certificate. Both chart refinement and its unit law are actual maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem refinedUnitBasisOfUnitBasis
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsOpenImmersion f] [IsOpenImmersion g] (T : Z.Modules)
    (p : (Scheme.Modules.restrictFunctor g).obj T ≅ SheafOfModules.unit Y.ringCatSheaf)
    (v : SheafOfModules.unit Z.ringCatSheaf ⟶ T)
    (hbase : (Scheme.Modules.restrictFunctor g).map v ≫ p.hom =
      (Scheme.Modules.restrictUnitIso g).hom) :
    (Scheme.Modules.restrictFunctor (f ≫ g)).map v ≫
      ((Scheme.Modules.restrictFunctorComp f g).app T).hom ≫
      (Scheme.Modules.restrictFunctor f).map p.hom ≫
      (Scheme.Modules.restrictUnitIso f).hom =
    (Scheme.Modules.restrictUnitIso (f ≫ g)).hom := by
  have h := cubicClosedPointSerreSurfaceJetCotangent_refinedSectionCoordinate f g T p v
  have hb : (Scheme.Modules.restrictUnitIso g).inv ≫
      (Scheme.Modules.restrictFunctor g).map v ≫ p.hom = 𝟙 _ :=
    (congrArg (fun k => (Scheme.Modules.restrictUnitIso g).inv ≫ k) hbase).trans
      (Iso.inv_hom_id (Scheme.Modules.restrictUnitIso g))
  rw [hb, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id] at h
  apply (cancel_epi (Scheme.Modules.restrictUnitIso (f ≫ g)).inv).1
  simpa only [Category.assoc, Iso.inv_hom_id] using h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma actualPositiveTwistRefinedChartUnitIso_basis
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (a : Fin 4) (m : ℕ) :
    let ell : grading I 1 := ⟨coordinate I a, coordinate_mem I a⟩
    let U := Proj.basicOpen (grading I) (coordinate I a)
    let e := Proj.basicOpenIsoSpec (grading I) (coordinate I a)
      (coordinate_mem I a) (by decide : 0 < 1)
    let T := positiveSheafOfModules (grading I) m
    (Scheme.Modules.restrictFunctor (chartι I a)).map
      (actualPositiveTwistChartBasisInvHom I ell m) ≫
      (cubicClosedPointSerreSurfaceJetCotangent_refinedChartUnitIso U e.inv T
        (actualPositiveTwistChartUnitIso I ell m)).hom =
    (Scheme.Modules.restrictUnitIso (chartι I a)).hom := by
  dsimp only
  exact refinedUnitBasisOfUnitBasis
    (Proj.basicOpenIsoSpec (grading I) (coordinate I a)
      (coordinate_mem I a) (by decide : 0 < 1)).inv
    (Proj.basicOpen (grading I) (coordinate I a)).ι
    (positiveSheafOfModules (grading I) m)
    (actualPositiveTwistChartUnitIso I ⟨coordinate I a, coordinate_mem I a⟩ m)
    (actualPositiveTwistChartBasisInvHom I ⟨coordinate I a, coordinate_mem I a⟩ m)
    (actualPositiveTwistChartUnitIso_basis I ⟨coordinate I a, coordinate_mem I a⟩ m)

end PfaffianDescent
