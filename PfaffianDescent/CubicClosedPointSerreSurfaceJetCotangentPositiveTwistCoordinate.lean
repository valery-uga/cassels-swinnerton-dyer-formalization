import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentPositiveTwistUnit
import PfaffianDescent.SchemeModuleLocalIsoGerm

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
set_option backward.isDefEq.respectTransparency false

/-- Actual restricted top-section coordinates are natural for an actual
ambient module morphism. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_restrictTopSectionIso_map
    {X : Scheme.{u}} (U : X.Opens) {M N : X.Modules} (a : M ⟶ N)
    (y : Γ(M, U)) :
    (schemeModuleRestrictTopSectionIso U N).hom
      (((Scheme.Modules.toPresheaf (U : Scheme)).map
          ((Scheme.Modules.restrictFunctor U.ι).map a)).app (op ⊤)
        ((schemeModuleRestrictTopSectionIso U M).inv y)) =
      ((Scheme.Modules.toPresheaf X).map a).app (op U) y := by
  unfold schemeModuleRestrictTopSectionIso
  simp only [Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    ConcreteCategory.comp_apply]
  change N.presheaf.map (eqToIso U.ι_image_top.symm).op.hom
    (((Scheme.Modules.toPresheaf X).map a).app (op (U.ι ''ᵁ ⊤))
      (M.presheaf.map (eqToIso U.ι_image_top.symm).op.inv y)) = _
  have hn := ((Scheme.Modules.toPresheaf X).map a).naturality
    (eqToIso U.ι_image_top.symm).op.hom
  have hny := congrArg (fun f => f (M.presheaf.map
    (eqToIso U.ι_image_top.symm).op.inv y)) hn
  simpa using hny.symm

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual positive-three section coefficients on the common linear chart. -/
def cubicClosedPointSerreSurfaceJetCotangent_positiveThreeSectionCoordinate
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1) :
    Γ(positiveSheafOfModules (grading I) 3, Proj.basicOpen (grading I) (ell : CoordinateRing I)) ≃+
      Γ(SheafOfModules.unit (scheme I).ringCatSheaf,
        Proj.basicOpen (grading I) (ell : CoordinateRing I)) := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  letI := cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom_isIso I ell
  exact (schemeModuleLocalSectionAddEquiv U
    (SheafOfModules.unit (scheme I).ringCatSheaf)
    (positiveSheafOfModules (grading I) 3)
    (asIso ((Scheme.Modules.restrictFunctor U.ι).map
      (cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom I ell)))).symm

/-- The actual coefficient of the actual homogeneous cubic section is the
actual affine function q/ell³. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveThreeSectionCoordinate_fraction
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (q : grading I 3) :
    cubicClosedPointSerreSurfaceJetCotangent_positiveThreeSectionCoordinate I ell
      ((positiveSheafOfModules (grading I) 3).presheaf.map
        (homOfLE (show Proj.basicOpen (grading I) (ell : CoordinateRing I) ≤ ⊤ from le_top)).op
        (PresheafOfModules.sections.eval
          (positiveGlobalSectionOfHomogeneous (grading I) 3 q) (op ⊤))) =
    (ProjectiveSpectrum.Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom
      (Away.mk (grading I) ell.2 3 (q : CoordinateRing I) (by simpa using q.2)) := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  let a := cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom I ell
  letI := cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom_isIso I ell
  let e := schemeModuleLocalSectionAddEquiv U
    (SheafOfModules.unit (scheme I).ringCatSheaf)
    (positiveSheafOfModules (grading I) 3)
    (asIso ((Scheme.Modules.restrictFunctor U.ι).map a))
  change e.symm _ = _
  apply e.injective
  rw [e.apply_symm_apply]
  change _ = (schemeModuleRestrictTopSectionIso U
    (positiveSheafOfModules (grading I) 3)).hom
    (((Scheme.Modules.toPresheaf (U : Scheme)).map
        ((Scheme.Modules.restrictFunctor U.ι).map a)).app (op ⊤)
      ((schemeModuleRestrictTopSectionIso U
        (SheafOfModules.unit (scheme I).ringCatSheaf)).inv _))
  rw [cubicClosedPointSerreSurfaceJetCotangent_restrictTopSectionIso_map]
  exact (cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom_fraction I ell q).symm

end PfaffianDescent
