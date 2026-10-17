import PfaffianDescent.ActualPositiveTwistChartFraction
/- SOURCE ONLY / UNVERIFIED. Actual chart-basis coefficients in every degree. -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def actualPositiveTwistChartSectionCoefficient
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) (ell : grading I 1) (m : ℕ) :
    Γ(positiveSheafOfModules (grading I) m, Proj.basicOpen (grading I) (ell : CoordinateRing I)) ≃+
      Γ(SheafOfModules.unit (scheme I).ringCatSheaf,
        Proj.basicOpen (grading I) (ell : CoordinateRing I)) := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  letI := actualPositiveTwistChartBasisInvHom_isIso I ell m
  exact (schemeModuleLocalSectionAddEquiv U
    (SheafOfModules.unit (scheme I).ringCatSheaf)
    (positiveSheafOfModules (grading I) m)
    (asIso ((Scheme.Modules.restrictFunctor U.ι).map
      (actualPositiveTwistChartBasisInvHom I ell m)))).symm

/-- The actual homogeneous section coefficient is its literal q/ell^m fraction. -/
theorem actualPositiveTwistChartSectionCoefficient_fraction
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ) (q : grading I m) :
    actualPositiveTwistChartSectionCoefficient I ell m
      ((positiveSheafOfModules (grading I) m).presheaf.map
        (homOfLE (show Proj.basicOpen (grading I) (ell : CoordinateRing I) ≤ ⊤ from le_top)).op
        (PresheafOfModules.sections.eval
          (positiveGlobalSectionOfHomogeneous (grading I) m q) (op ⊤))) =
    (ProjectiveSpectrum.Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom
      (Away.mk (grading I) ell.2 m (q : CoordinateRing I) (by simpa using q.2)) := by
  let U := Proj.basicOpen (grading I) (ell : CoordinateRing I)
  let a := actualPositiveTwistChartBasisInvHom I ell m
  letI := actualPositiveTwistChartBasisInvHom_isIso I ell m
  let e := schemeModuleLocalSectionAddEquiv U
    (SheafOfModules.unit (scheme I).ringCatSheaf)
    (positiveSheafOfModules (grading I) m)
    (asIso ((Scheme.Modules.restrictFunctor U.ι).map a))
  change e.symm _ = _
  apply e.injective
  rw [e.apply_symm_apply]
  change _ = (schemeModuleRestrictTopSectionIso U
    (positiveSheafOfModules (grading I) m)).hom
    (((Scheme.Modules.toPresheaf (U : Scheme)).map
        ((Scheme.Modules.restrictFunctor U.ι).map a)).app (op ⊤)
      ((schemeModuleRestrictTopSectionIso U
        (SheafOfModules.unit (scheme I).ringCatSheaf)).inv _))
  rw [cubicClosedPointSerreSurfaceJetCotangent_restrictTopSectionIso_map]
  exact (actualPositiveTwistChartBasisInvHom_fraction I ell m q).symm

lemma actualPositiveTwistChartSectionCoefficient_homogeneousFamily
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (ell : grading I 1) (m : ℕ) (q : grading I m) :
    actualPositiveTwistChartSectionCoefficient I ell m
      ((positiveGlobalSectionOfHomogeneous (grading I) m q).val
        (op (Proj.basicOpen (grading I) (ell : CoordinateRing I)))) =
    (Proj.awayToSection (grading I) (ell : CoordinateRing I)).hom
      (Away.mk (grading I) ell.2 m (q : CoordinateRing I) (by simpa using q.2)) := by
  have h := actualPositiveTwistChartSectionCoefficient_fraction I ell m q
  have hs : (positiveSheafOfModules (grading I) m).presheaf.map
      (homOfLE (show Proj.basicOpen (grading I) (ell : CoordinateRing I) ≤ ⊤ from le_top)).op
      (PresheafOfModules.sections.eval
        (positiveGlobalSectionOfHomogeneous (grading I) m q) (op ⊤)) =
    (positiveGlobalSectionOfHomogeneous (grading I) m q).val
      (op (Proj.basicOpen (grading I) (ell : CoordinateRing I))) :=
    (positiveGlobalSectionOfHomogeneous (grading I) m q).property
      (homOfLE (show Proj.basicOpen (grading I) (ell : CoordinateRing I) ≤ ⊤ from le_top)).op
  rw [hs] at h
  exact h

end PfaffianDescent
