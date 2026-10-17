import PfaffianDescent.CubicFieldChartSerreRankSpecialization
import PfaffianDescent.CubicGroundKernelJetPointOriginalSupport

/-! The retained native rank chart is specialized at three literal
extensions of the SAME original support point. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicFieldChartSerreRankSpecialization_support
    {F L E : Type u} [Field F] [Field L] [Field E] [Algebra F L] [Algebra F E]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3)
    (ell : grading (equationIdeal P hP) 1)
    (g : Away (grading (equationIdeal P hP))
      (ell : CoordinateRing (equationIdeal P hP)) →+* L)
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
      (show (hypersurface P hP).Modules from e.E)) = 9)
    (hdata : CubicFieldChartSerreRankSpecialization (E := E) P hP ell g e C h9) :
    ∃ α : Fin 3 → (L →ₐ[F] E),
      letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
        (show (hypersurface P hP).Modules from e.E)) :=
        Module.finite_of_finrank_pos (by rw [h9]; decide)
      SerreActualConfigurationRankChartAtPoint (hypersurfaceToBase P hP) e C h9
        (fun n => Spec.map (CommRingCat.ofHom (α n).toRingHom) ≫
          cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
            (equationIdeal P hP) ell g) := by
  letI : FiniteDimensional F (SchemeModuleGlobalSectionsOver (hypersurfaceToBase P hP)
      (show (hypersurface P hP).Modules from e.E)) :=
    Module.finite_of_finrank_pos (by rw [h9]; decide)
  obtain ⟨φ, α, hres, hrank⟩ := hdata
  have hpoints : (fun n => cubicGroundKernelJetPoint (equationIdeal P hP) ell (φ n)) =
      (fun n => Spec.map (CommRingCat.ofHom (α n).toRingHom) ≫
        cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
          (equationIdeal P hP) ell g) := by
    funext n
    exact cubicGroundKernelJetPoint_factors_original_support
      (equationIdeal P hP) ell g (φ n) (α n).toRingHom (hres n)
  rw [hpoints] at hrank
  exact ⟨α, hrank⟩

end PfaffianDescent
