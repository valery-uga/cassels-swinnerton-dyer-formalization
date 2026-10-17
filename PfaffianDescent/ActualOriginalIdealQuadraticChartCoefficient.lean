import PfaffianDescent.ActualOriginalNativeQuadraticSectionInclusion
import PfaffianDescent.ActualPositiveTwistChartSectionCoefficient

/- SOURCE ONLY / UNVERIFIED. Actual original ambient H0 section, restricted
through the original cubic ideal and the derived native O2, has the literal
normalized quadratic coefficient on EVERY original coordinate chart.
No chart comparison, ideal-map square or tangent certificate is assumed. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

def actualOriginalAmbientIdealQuadraticChartCoefficient
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) (j : Fin 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    Γ(SheafOfModules.unit (hypersurface p hp).ringCatSheaf,
      Proj.basicOpen (grading (equationIdeal p hp)) (coordinate (equationIdeal p hp) j)) := by
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let N := positiveSheafOfModules (grading I) 2
  exact actualPositiveTwistChartSectionCoefficient I ell 2
    ((N.unitHomEquiv
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s ≫
        actualIdealTwistInclusion q N)).val
      (op (Proj.basicOpen (grading I) (coordinate I j))))

lemma actualOriginalAmbientIdealQuadraticChartCoefficient_eq_native
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (P : closedPoints (hypersurface p hp)) (j : Fin 4)
    (s : ActualOriginalPointIdealQuadraticSections p hp P) :
    let I := equationIdeal p hp
    let q := (hypersurface p hp).fromSpecResidueField P.1
    let i := quotientProjMap I
    letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
    letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
    actualOriginalAmbientIdealQuadraticChartCoefficient p hp P j s =
      (Proj.awayToSection (grading I) (coordinate I j)).hom
        (aeval (chartCoordinate I j)
          (p3ActualIdealQuadraticIntrinsicLinearEquiv (q ≫ i) s).val) := by
  dsimp only
  let I := equationIdeal p hp
  let q := (hypersurface p hp).fromSpecResidueField P.1
  let i := quotientProjMap I
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion i := quotientProjMap_isClosedImmersion I
  letI : IsClosedImmersion (q ≫ i) := IsClosedImmersion.comp q i
  letI : Algebra K (ChartRing I j) := (chartBaseMap I j).toAlgebra
  let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
  let N := positiveSheafOfModules (grading I) 2
  let Q : homogeneousSubmodule (Fin 4) K 2 :=
    ⟨(p3ActualIdealQuadraticIntrinsicLinearEquiv (q ≫ i) s).val,
      (p3ActualIdealQuadraticIntrinsicLinearEquiv (q ≫ i) s).property.1⟩
  let QI : grading I 2 :=
    ⟨Ideal.Quotient.mk I.toIdeal Q, (quotientGradedRingHom I).2 Q.property⟩
  change actualPositiveTwistChartSectionCoefficient I ell 2
    ((N.unitHomEquiv
      (actualOriginalAmbientIdealQuadraticNativeTwistRestriction p hp P s ≫
        actualIdealTwistInclusion q N)).val
      (op (Proj.basicOpen (grading I) (coordinate I j)))) = _
  have h := congrArg (fun a : schemeModuleUnit (hypersurface p hp) ⟶ N =>
    actualPositiveTwistChartSectionCoefficient I ell 2
      ((N.unitHomEquiv a).val
        (op (Proj.basicOpen (grading I) (coordinate I j)))))
    (actualOriginalAmbientIdealQuadraticNativeTwistRestriction_inclusion p hp P s)
  have hfamily := congrArg (fun t : N.sections =>
    actualPositiveTwistChartSectionCoefficient I ell 2
      (t.val (op (Proj.basicOpen (grading I) (coordinate I j)))))
    (N.unitHomEquiv.apply_symm_apply
      (positiveGlobalSectionOfHomogeneous (grading I) 2 QI))
  exact h.trans (hfamily.trans
    ((actualPositiveTwistChartSectionCoefficient_homogeneousFamily I ell 2 QI).trans
      (congrArg (Proj.awayToSection (grading I) (coordinate I j)).hom
        (actualChartHomogeneousFraction_eq_aeval I j 2 Q))))

end PfaffianDescent
