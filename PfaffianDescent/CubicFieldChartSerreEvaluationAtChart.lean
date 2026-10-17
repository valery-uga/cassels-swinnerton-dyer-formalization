import PfaffianDescent.CubicFieldChartSerreEvaluationBundle
import PfaffianDescent.CubicFieldPointChartSerreExistence
import PfaffianDescent.CubicClosedPointSerreFreeNeighborhoodNativeSerreData
import PfaffianDescent.SerreConnectingProductNonzero

/-! Actual Serre-extension witnesses at one fixed actual chart point. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def CubicFieldChartSerreEvaluationAtChart
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L] [Algebra F E]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (ell : grading (equationIdeal P hP) 1)
    (g : Away (grading (equationIdeal P hP)) (ell : CoordinateRing (equationIdeal P hP)) →+* L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal P hP) ell g)]
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal P hP))
      (z := (ell : CoordinateRing (equationIdeal P hP)))) = algebraMap F L) : Prop :=
    let I := equationIdeal P hP
    let iG := cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g
    letI : HasExt.{u} (hypersurface P hP).Modules := schemeModules_hasExt _
    letI : HasExt.{u} (Proj (grading I)).Modules := schemeModules_hasExt _
    letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits I 3
    letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits I 3
    ∃ (e : SerreExtensionData (hypersurface P hP)
      (closedImmersionIdealTwist iG (positiveSheafOfModules (grading I) 3)))
      (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e),
      SerreConnectingProductNonzero iG (positiveSheafOfModules (grading I) 3) e.toSequenceData ∧
      finrank F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
        (show (hypersurface P hP).Modules from e.E)) = 9 ∧
      CubicFieldChartSerreBundleEvaluation (E := E) I ell g hbase e.E e.projection

theorem cubicFieldChartSerreEvaluationAtChart_of_witnesses
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L] [Algebra F E]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (ell : grading (equationIdeal P hP) 1)
    (g : Away (grading (equationIdeal P hP)) (ell : CoordinateRing (equationIdeal P hP)) →+* L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal P hP) ell g)]
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal P hP))
      (z := (ell : CoordinateRing (equationIdeal P hP)))) = algebraMap F L) :
    let I := equationIdeal P hP
    let iG := cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion I ell g
    letI : HasExt.{u} (hypersurface P hP).Modules := schemeModules_hasExt _
    letI : HasExt.{u} (Proj (grading I)).Modules := schemeModules_hasExt _
    letI := quotientPositiveTwist_tensorRight_preservesFiniteLimits I 3
    letI := quotientPositiveTwist_tensorRight_preservesFiniteColimits I 3
    ∀ (e : SerreExtensionData (hypersurface P hP)
      (closedImmersionIdealTwist iG (positiveSheafOfModules (grading I) 3)))
      (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e),
      SerreConnectingProductNonzero iG (positiveSheafOfModules (grading I) 3) e.toSequenceData →
      finrank F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
        (show (hypersurface P hP).Modules from e.E)) = 9 →
      CubicFieldChartSerreBundleEvaluation (E := E) I ell g hbase e.E e.projection →
      CubicFieldChartSerreEvaluationAtChart (E := E) P hP ell g hbase := by
  dsimp only
  intro e C hne h9 hEval
  exact ⟨e, C, hne, h9, hEval⟩

end PfaffianDescent
