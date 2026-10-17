import PfaffianDescent.SerreActualConfigurationRankFactory
import PfaffianDescent.CubicFieldChartSerreEvaluationBundle
import PfaffianDescent.VoisinGenericCubicResidual

/-! An actual cubic Serre bundle's native six-dimensional evaluation
constructs the actual principal rank chart. Cubic geometric integrality and
finite-dimensionality are derived internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldChartSerreBundleEvaluation_actual_configurationRank
    {F L E : Type u} [Field F] [CharZero F] [Field L] [Field E]
    [Algebra F L] [Algebra F E]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    (ell : grading (equationIdeal P hP) 1)
    (g : Away (grading (equationIdeal P hP))
      (ell : CoordinateRing (equationIdeal P hP)) →+* L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal P hP) ell g)]
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading (equationIdeal P hP))
      (z := (ell : CoordinateRing (equationIdeal P hP)))) = algebraMap F L)
    (e : SerreExtensionData (hypersurface P hP)
      (closedImmersionIdealTwist
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
          (equationIdeal P hP) ell g)
        (positiveSheafOfModules (grading (equationIdeal P hP)) 3)))
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (h9 : finrank F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
      (show (hypersurface P hP).Modules from e.E)) = 9)
    (hEval : CubicFieldChartSerreBundleEvaluation (E := E)
      (equationIdeal P hP) ell g hbase e.E e.projection) :
    letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
      (show (hypersurface P hP).Modules from e.E)) :=
      Module.finite_of_finrank_pos (by rw [h9]; decide)
    SerreActualConfigurationRankChart (hypersurfaceToBase P hP) e C h9 := by
  letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
      (show (hypersurface P hP).Modules from e.E)) :=
    Module.finite_of_finrank_pos (by rw [h9]; decide)
  letI : GeometricallyIntegral (hypersurfaceToBase P hP) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_infinite P hP hP0
  obtain ⟨φ, α, hres, honto, hbij⟩ := hEval
  exact serreActualConfigurationRankChart_of_actual_evaluation
    (hypersurfaceToBase P hP) e C h9
    (fun i => cubicGroundKernelJetPoint (equationIdeal P hP) ell (φ i))
    (fun i => cubicGroundKernelJetPoint_toBase (equationIdeal P hP)
      ell g hbase (φ i) (α i) (hres i)) honto

end PfaffianDescent
