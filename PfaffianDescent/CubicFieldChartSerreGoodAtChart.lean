import PfaffianDescent.CubicFieldChartSerreEvaluationAtChart
import PfaffianDescent.CubicFieldChartSerrePlaneAtChart
import PfaffianDescent.CubicGroundKernelOriginalSupportBase
import PfaffianDescent.SerreActualConfigurationGenericGoodData

/-! The SAME actual Serre bundle and evaluation witnesses also carry an
actual integral plane incidence and a good simple-zero parameter at the generic configuration. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def CubicFieldChartSerreGoodAtChart
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
      (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
      (h9 : finrank F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
        (show (hypersurface P hP).Modules from e.E)) = 9),
      SerreConnectingProductNonzero iG (positiveSheafOfModules (grading I) 3) e.toSequenceData ∧
      CubicFieldChartSerreBundleEvaluation (E := E) I ell g hbase e.E e.projection ∧
      letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
        (show (hypersurface P hP).Modules from e.E)) :=
        Module.finite_of_finrank_pos (by rw [h9]; decide)
      SerreActualConfigurationGenericGoodData (hypersurfaceToBase P hP) e C h9

theorem cubicFieldChartSerreGoodAtChart_of_actual_evaluation
    {F L E : Type u} [Field F] [CharZero F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] [FiniteDimensional F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    (ell : grading (equationIdeal P hP) 1)
    (g : Away (grading (equationIdeal P hP)) (ell : CoordinateRing (equationIdeal P hP)) →+* L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal P hP) ell g)]
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal P hP))
      (z := (ell : CoordinateRing (equationIdeal P hP)))) = algebraMap F L)
    (hdata : CubicFieldChartSerreEvaluationAtChart (E := E) P hP ell g hbase) :
    CubicFieldChartSerreGoodAtChart (E := E) P hP ell g hbase := by
  have hRetained := cubicFieldChartSerrePlaneAtChart_of_actual_evaluation
    P hP hP0 ell g hbase hdata
  obtain ⟨e, C, h9, hne, hEval, α, hPlane⟩ := hRetained
  refine ⟨e, C, h9, hne, hEval, ?_⟩
  letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
      (show (hypersurface P hP).Modules from e.E)) :=
    Module.finite_of_finrank_pos (by rw [h9]; decide)
  exact cubicClosedPointSerreGenericGoodData_of_retained_plane P hP hP0
    (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal P hP) ell g)
    (cubicGroundKernelOriginalSupport_toBase (equationIdeal P hP) ell g hbase)
    e C h9 α hPlane

end PfaffianDescent
