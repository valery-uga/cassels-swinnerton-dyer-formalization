import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveTwistCoordinate

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false
private theorem inverseLocalStalkCoordinate_germ
    {X : Scheme.{u}} (U : X.Opens) (x : U) (M N : X.Modules)
    (e : M.restrict U.ι ≅ N.restrict U.ι) (y : Γ(N, U)) :
    (schemeModuleLocalStalkAddEquiv U x M N e).symm
      (N.presheaf.germ U (U.ι x) x.2 y) =
    M.presheaf.germ U (U.ι x) x.2
      ((schemeModuleLocalSectionAddEquiv U M N e).symm y) := by
  let es := schemeModuleLocalSectionAddEquiv U M N e
  let et := schemeModuleLocalStalkAddEquiv U x M N e
  apply et.injective
  rw [et.apply_symm_apply]
  exact (schemeModuleLocalStalkAddEquiv_germ U x M N e (es.symm y)).trans
    (congrArg (fun z => N.presheaf.germ U (U.ι x) x.2 z) (es.apply_symm_apply y)) |>.symm

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- The actual inverse cubic-twist coordinate at an actual point of the common chart. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveThreeStalkCoordinate
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (x : Proj.basicOpen (grading I) (ell : CoordinateRing I)) :
    (positiveSheafOfModules (grading I) 3).presheaf.stalk ((Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι x) ≃+
      ((Scheme.Modules.toPresheaf (scheme I)).obj (SheafOfModules.unit (scheme I).ringCatSheaf)).stalk ((Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι x) := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  letI := cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom_isIso I ell
  exact (schemeModuleLocalStalkAddEquiv U x
    (SheafOfModules.unit (scheme I).ringCatSheaf)
    (positiveSheafOfModules (grading I) 3)
    (asIso ((Scheme.Modules.restrictFunctor U.ι).map
      (cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom I ell)))).symm

/-- The actual inverse stalk coordinate and the actual section coordinate commute with germs. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveThreeStalkCoordinate_germ
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (x : Proj.basicOpen (grading I) (ell : CoordinateRing I))
    (y : Γ(positiveSheafOfModules (grading I) 3,
      Proj.basicOpen (grading I) (ell : CoordinateRing I))) :
    cubicClosedPointSerreSurfaceJetCotangent_positiveThreeStalkCoordinate I ell x
      ((positiveSheafOfModules (grading I) 3).presheaf.germ _ ((Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι x) x.2 y) =
    ((Scheme.Modules.toPresheaf (scheme I)).obj (SheafOfModules.unit (scheme I).ringCatSheaf)).germ _ ((Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι x) x.2
      (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeSectionCoordinate I ell y) := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  letI := cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom_isIso I ell
  exact inverseLocalStalkCoordinate_germ U x
    (SheafOfModules.unit (scheme I).ringCatSheaf)
    (positiveSheafOfModules (grading I) 3)
    (asIso ((Scheme.Modules.restrictFunctor U.ι).map
      (cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom I ell))) y

/-- The actual cubic section germ has actual coefficient germ q/ell³. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveThreeStalkCoordinate_fraction
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (x : Proj.basicOpen (grading I) (ell : CoordinateRing I)) (q : grading I 3) :
    cubicClosedPointSerreSurfaceJetCotangent_positiveThreeStalkCoordinate I ell x
      ((positiveSheafOfModules (grading I) 3).presheaf.germ _ ((Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι x) x.2
        ((positiveSheafOfModules (grading I) 3).presheaf.map
          (homOfLE (show Proj.basicOpen (grading I) (ell : CoordinateRing I) ≤ ⊤ from le_top)).op
          (PresheafOfModules.sections.eval
            (positiveGlobalSectionOfHomogeneous (grading I) 3 q) (op ⊤)))) =
    ((Scheme.Modules.toPresheaf (scheme I)).obj (SheafOfModules.unit (scheme I).ringCatSheaf)).germ _ ((Proj.basicOpen (grading I) (ell : CoordinateRing I)).ι x) x.2
      ((ProjectiveSpectrum.Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom
        (Away.mk (grading I) ell.2 3 (q : CoordinateRing I) (by simpa using q.2))) := by
  rw [cubicClosedPointSerreSurfaceJetCotangent_positiveThreeStalkCoordinate_germ,
    cubicClosedPointSerreSurfaceJetCotangent_positiveThreeSectionCoordinate_fraction]

end PfaffianDescent
