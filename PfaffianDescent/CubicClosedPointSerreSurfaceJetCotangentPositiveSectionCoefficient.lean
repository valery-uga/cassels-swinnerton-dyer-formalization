import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentSectionChartCoefficient

noncomputable section
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreSurfaceJetCotangent_localUnitCoefficientOfBasis
    {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)
    (e : (Scheme.Modules.restrictFunctor U.ι).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅ (Scheme.Modules.restrictFunctor U.ι).obj M)
    (y : Γ(M, U)) :
    schemeModuleLocalUnitSectionAddEquiv U M
      (e.symm ≪≫ Scheme.Modules.restrictUnitIso U.ι) y =
    (schemeModuleLocalSectionAddEquiv U
      (SheafOfModules.unit X.ringCatSheaf) M e).symm y := by
  unfold schemeModuleLocalUnitSectionAddEquiv
  have he : (e.symm ≪≫ Scheme.Modules.restrictUnitIso U.ι) ≪≫
      (Scheme.Modules.restrictUnitIso U.ι).symm = e.symm := by
    ext
    simp
  rw [he]
  rfl

/-- Literal unit coordinate of the actual positive cubic section. -/
theorem cubicClosedPointSerreSurfaceJetCotangent_positiveSectionCoefficient
    {K : Type u} [Field K]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1)
    (q : grading I 3) :
    schemeModuleLocalUnitSectionAddEquiv
      (Proj.basicOpen (grading I) (ell : CoordinateRing I))
      (positiveSheafOfModules (grading I) 3)
      (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeUnitIso I ell)
      ((positiveGlobalSectionOfHomogeneous (grading I) 3 q).val
        (op (Proj.basicOpen (grading I) (ell : CoordinateRing I)))) =
    (ProjectiveSpectrum.Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom
      (Away.mk (grading I) ell.2 3 (q : CoordinateRing I) (by simpa using q.2)) := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  letI := cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom_isIso I ell
  have hb := cubicClosedPointSerreSurfaceJetCotangent_localUnitCoefficientOfBasis U
    (positiveSheafOfModules (grading I) 3)
    (asIso ((Scheme.Modules.restrictFunctor U.ι).map
      (cubicClosedPointSerreSurfaceJetCotangent_positiveChartBasisInvHom I ell)))
    ((positiveGlobalSectionOfHomogeneous (grading I) 3 q).val (op U))
  have hq := cubicClosedPointSerreSurfaceJetCotangent_positiveThreeSectionCoordinate_fraction I ell q
  have hs := (positiveGlobalSectionOfHomogeneous (grading I) 3 q).property
    (homOfLE (show U ≤ ⊤ from le_top)).op
  exact hb.trans ((congrArg
    (cubicClosedPointSerreSurfaceJetCotangent_positiveThreeSectionCoordinate I ell) hs).symm.trans hq)

end PfaffianDescent
