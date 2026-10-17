import PfaffianDescent.IncidenceSheafSections

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
section
variable (K : Type u) [CommRing K] (U : (grassmannianScheme K 3 3).Opens)

noncomputable def incidenceChartRestrictedMatrix (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    Matrix (Fin 3) (Fin 3) Γ(grassmannianChartScheme K 3 3, (grassmannianChartι K σ) ⁻¹ᵁ U) :=
  (grassmannianChartRegularMatrix K).map
    (regularFunctionRestrict (grassmannianChartScheme K 3 3) ((grassmannianChartι K σ) ⁻¹ᵁ U))

/-- On sections, the chart sheaf morphism is exactly the actual alternating restriction matrix. -/
lemma incidenceChartRestrictionSheafMap_sections (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (c : AlternatingTripleIndex → Γ(grassmannianScheme K 3 3, U)) :
    (incidenceChartRestrictionSheafMap K σ).val.app (op U) c =
      incidenceRestrictionMap Γ(grassmannianChartScheme K 3 3, (grassmannianChartι K σ) ⁻¹ᵁ U)
        σ (incidenceChartRestrictedMatrix K U σ) (((grassmannianChartι K σ).app U).hom ∘ c) := by
  classical
  let ρ := regularFunctionRestrict (grassmannianChartScheme K 3 3) ((grassmannianChartι K σ) ⁻¹ᵁ U)
  let d := ((grassmannianChartι K σ).app U).hom ∘ c
  change Matrix.toLin' ((incidenceRestrictionMatrix _ σ (grassmannianChartRegularMatrix K)).map ρ) d = _
  have hm := incidenceRestrictionMatrix_map ρ σ (grassmannianChartRegularMatrix K)
  exact (congrArg (fun P => Matrix.toLin' P d) hm).trans
    (congrArg (fun f => f d) (incidenceRestrictionMatrix_toLin _ σ (incidenceChartRestrictedMatrix K U σ)))

/-- Sections of the global kernel sheaf satisfy exactly the actual tautological isotropy equations on each chart. -/
theorem mem_incidenceEquationSections_isotropic
    (c : AlternatingTripleIndex → Γ(grassmannianScheme K 3 3, U)) :
    c ∈ incidenceEquationSections K U ↔ ∀ σ, ∀ k,
      alternatingRestriction Γ(grassmannianChartScheme K 3 3, (grassmannianChartι K σ) ⁻¹ᵁ U) _
        (grassmannianChartSubmodule _ σ (incidenceChartRestrictedMatrix K U σ))
        ((alternatingCoordinates (incidenceAmbientBasis _)).symm
          (fun s => (grassmannianChartι K σ).app U (c (k, s)))) = 0 := by
  rw [mem_incidenceEquationSections]
  apply forall_congr'
  intro σ
  rw [incidenceChartRestrictionSheafMap_sections]
  exact incidenceRestrictionMap_eq_zero_iff _ σ (incidenceChartRestrictedMatrix K U σ) _

end
end PfaffianDescent
