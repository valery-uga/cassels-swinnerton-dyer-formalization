import PfaffianDescent.CubicFieldChartSerreEvaluationAtChart
import PfaffianDescent.CubicFieldChartSerreRankSupport
import PfaffianDescent.SerreActualConfigurationPlanePoint

/-! The SAME actual Serre bundle and evaluation witnesses also carry an
actual integral plane incidence and the SAME original support witness point. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def CubicFieldChartSerrePlaneAtChart
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
      ∃ α : Fin 3 → (L →ₐ[F] E),
        SerreActualConfigurationPlaneDataAtPoint (hypersurfaceToBase P hP) e C h9
          (fun n => Spec.map (CommRingCat.ofHom (α n).toRingHom) ≫ iG)

theorem cubicFieldChartSerrePlaneAtChart_of_actual_evaluation
    {F L E : Type u} [Field F] [CharZero F] [Field L] [Field E]
    [Algebra F L] [Algebra F E]
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
    CubicFieldChartSerrePlaneAtChart (E := E) P hP ell g hbase := by
  obtain ⟨e, C, hne, h9, hEval⟩ := hdata
  refine ⟨e, C, h9, hne, hEval, ?_⟩
  letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
      (show (hypersurface P hP).Modules from e.E)) :=
    Module.finite_of_finrank_pos (by rw [h9]; decide)
  have hSpec := cubicFieldChartSerreRankSpecialization_of_actual_evaluation
    P hP hP0 ell g hbase e C h9 hEval
  obtain ⟨α, hrank⟩ := cubicFieldChartSerreRankSpecialization_support P hP ell g e C h9 hSpec
  refine ⟨α, ?_⟩
  exact serreActualConfigurationPlaneDataAtPoint_of_rank_chart
    (hypersurfaceToBase P hP) e C h9 _ hrank

end PfaffianDescent
