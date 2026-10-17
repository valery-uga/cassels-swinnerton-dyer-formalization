import AllCharacteristics.HomogeneousProjectiveAmbient

/-! SOURCE ONLY. A genuine ambient-compatible scheme morphism from a
relevant homogeneous prime recovers containment in its FULL ideal. -/
noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality.GeometricLines215
open MvPolynomial AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
universe u
variable {E : Type u} [Field E]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fullIdeal_le_of_actual_projective_factor215
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
    (hIprime : I.toIdeal.IsPrime)
    (hIrelevant : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) E) ≤ I)
    (c : scheme I ⟶ scheme J)
    (hAmbient : c ≫ quotientProjMap J = quotientProjMap I) :
    J.toIdeal ≤ I.toIdeal := by
  let z : ProjectiveSpectrum (homogeneousSubmodule (Fin 4) E) :=
    ⟨I, hIprime, hIrelevant⟩
  have hzI : z ∈ Set.range (quotientProjMap I) :=
    (quotientProjMap_mem_range_iff I z).mpr le_rfl
  obtain ⟨y, hy⟩ := hzI
  have hzJ : z ∈ Set.range (quotientProjMap J) := by
    refine ⟨c y, ?_⟩
    rw [← Scheme.Hom.comp_apply, hAmbient]
    exact hy
  exact (quotientProjMap_mem_range_iff J z).mp hzJ

theorem original_equation_mem_of_actual_line_to_cubic215
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
    (hIprime : I.toIdeal.IsPrime)
    (hIrelevant : ¬ HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 4) E) ≤ I)
    (F : MvPolynomial (Fin 4) E) (hF : F.IsHomogeneous 3)
    (c : scheme I ⟶ hypersurface F hF)
    (hAmbient : c ≫ hypersurfaceToAmbient F hF = quotientProjMap I) :
    F ∈ I.toIdeal := by
  have hle := fullIdeal_le_of_actual_projective_factor215 I
    (equationIdeal F hF) hIprime hIrelevant c hAmbient
  exact hle (Ideal.subset_span (Set.mem_singleton F))

end PfaffianDescent.QuadraticSkewRationality.GeometricLines215
