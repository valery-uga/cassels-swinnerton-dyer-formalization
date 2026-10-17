import PfaffianDescent.SerreActualConfigurationRankPoint
import PfaffianDescent.CubicFieldChartSerreRankEvaluation

/-! The native rank chart retains a specialization at the SAME original
degree-eleven point, via the actual jet residue maps. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

def CubicFieldChartSerreRankSpecialization
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L] [Algebra F E]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (ell : grading (equationIdeal P hP) 1)
    (g : Away (grading (equationIdeal P hP)) (ell : CoordinateRing (equationIdeal P hP)) →+* L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal P hP) ell g)]
    (e : SerreExtensionData (hypersurface P hP)
      (closedImmersionIdealTwist
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
          (equationIdeal P hP) ell g)
        (positiveSheafOfModules (grading (equationIdeal P hP)) 3)))
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (h9 : finrank F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
      (show (hypersurface P hP).Modules from e.E)) = 9) : Prop :=
    ∃ (φ : Fin 3 → (Away (grading (equationIdeal P hP))
      (ell : CoordinateRing (equationIdeal P hP)) →+* CubicSurfaceFirstJet E))
      (α : Fin 3 → (L →ₐ[F] E))
      (_ : ∀ i, cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap (φ i) =
        (α i).toRingHom.comp g),
      letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
        (show (hypersurface P hP).Modules from e.E)) :=
        Module.finite_of_finrank_pos (by rw [h9]; decide)
      SerreActualConfigurationRankChartAtPoint (hypersurfaceToBase P hP) e C h9
        (fun i => cubicGroundKernelJetPoint (equationIdeal P hP) ell (φ i))

theorem cubicFieldChartSerreRankSpecialization_of_actual_evaluation
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
    CubicFieldChartSerreRankSpecialization (E := E) P hP ell g e C h9 := by
  letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
      (show (hypersurface P hP).Modules from e.E)) :=
    Module.finite_of_finrank_pos (by rw [h9]; decide)
  letI : GeometricallyIntegral (hypersurfaceToBase P hP) :=
    geometricallyIntegral_hypersurfaceToBase_of_smooth_of_infinite P hP hP0
  obtain ⟨φ, α, hres, honto, hbij⟩ := hEval
  refine ⟨φ, α, hres, ?_⟩
  exact serreActualConfigurationRankChartAtPoint_of_actual_evaluation
    (hypersurfaceToBase P hP) e C h9
    (fun i => cubicGroundKernelJetPoint (equationIdeal P hP) ell (φ i))
    (fun i => cubicGroundKernelJetPoint_toBase (equationIdeal P hP)
      ell g hbase (φ i) (α i) (hres i)) honto

end PfaffianDescent
