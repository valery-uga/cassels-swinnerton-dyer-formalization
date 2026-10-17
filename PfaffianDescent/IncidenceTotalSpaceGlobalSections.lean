import PfaffianDescent.IncidenceSectionGluing

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
section
variable (K : Type u) [CommRing K]

/-- The standard Grassmannian chart cover restricted to an arbitrary open. -/
noncomputable def incidenceSectionChartOpen (U : (grassmannianScheme K 3 3).Opens)
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) : (grassmannianScheme K 3 3).Opens :=
  U ⊓ (grassmannianChartι K σ).opensRange

lemma incidenceSectionChartOpen_le (U : (grassmannianScheme K 3 3).Opens)
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) : incidenceSectionChartOpen K U σ ≤ U := inf_le_left

lemma incidenceSectionChartOpen_chart (U : (grassmannianScheme K 3 3).Opens)
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) :
    incidenceSectionChartOpen K U σ ≤ (grassmannianChartι K σ).opensRange := inf_le_right

lemma incidenceSectionChartOpen_cover (U : (grassmannianScheme K 3 3).Opens) :
    U ≤ ⨆ σ, incidenceSectionChartOpen K U σ := by
  intro x hx
  rw [TopologicalSpace.Opens.mem_iSup]
  obtain ⟨i, y, hy⟩ := (grassmannianGlueData K 3 3).openCover.exists_eq x
  exact ⟨i.down, hx, y, hy⟩

/-- Every actual incidence scheme section determines a unique section of the global kernel sheaf. -/
theorem incidenceSchemeSection_kernel_exists (U : (grassmannianScheme K 3 3).Opens)
    (s : IncidenceSchemeSections K U) :
    ∃! x : Γ(incidenceKernelSheaf K, U),
      (incidenceKernelSheafι K).val.app (op U) x = incidenceSchemeSectionCoefficients K U s := by
  let V := incidenceSectionChartOpen K U
  let hV := incidenceSectionChartOpen_le K U
  let hc := incidenceSectionChartOpen_chart K U
  let t := fun σ => incidenceSchemeKernelSectionsOnChart K σ (V σ) (hc σ)
    (incidenceSchemeSectionsRestrict K U (V σ) (hV σ) s)
  have ht : ∀ σ τ, incidenceKernelSectionRestrict K (V σ) (V σ ⊓ V τ) inf_le_left (t σ) =
      incidenceKernelSectionRestrict K (V τ) (V σ ⊓ V τ) inf_le_right (t τ) := by
    intro σ τ
    dsimp only [t]
    rw [← incidenceSchemeKernelSectionsOnChart_restrict,
      ← incidenceSchemeKernelSectionsOnChart_restrict,
      incidenceSchemeSectionsRestrict_trans, incidenceSchemeSectionsRestrict_trans]
    exact incidenceSchemeKernelSectionsOnChart_independent K σ τ _ _ _ _
  obtain ⟨x, hx, _⟩ := schemeModuleSections_glue (incidenceKernelSheaf K) U V hV
    (incidenceSectionChartOpen_cover K U) t ht
  have he : (incidenceKernelSheafι K).val.app (op U) x =
      incidenceSchemeSectionCoefficients K U s := by
    apply schemeModuleSections_ext (coordinateModuleSheaf (grassmannianScheme K 3 3) AlternatingTripleIndex)
      U V hV (incidenceSectionChartOpen_cover K U)
    intro σ
    change regularFunctionRestrictFrom (grassmannianScheme K 3 3) U (V σ) (hV σ) ∘
        ((incidenceKernelSheafι K).val.app (op U) x) =
      regularFunctionRestrictFrom (grassmannianScheme K 3 3) U (V σ) (hV σ) ∘
        incidenceSchemeSectionCoefficients K U s
    exact (incidenceKernelSectionRestrict_coefficients K U (V σ) (hV σ) x).symm.trans
      ((congrArg ((incidenceKernelSheafι K).val.app (op (V σ))) (hx σ)).trans
        ((incidenceSchemeKernelSectionsOnChart_coefficients K σ (V σ) (hc σ) _).trans
          (incidenceSchemeSectionCoefficients_restrict K U (V σ) (hV σ) s)))
  exact ⟨x, he, fun y hy => incidenceKernelSheafι_sections_injective K U (hy.trans he.symm)⟩

/-- The global kernel section associated to an actual section of the incidence scheme. -/
noncomputable def incidenceSchemeToKernelSection (U : (grassmannianScheme K 3 3).Opens)
    (s : IncidenceSchemeSections K U) : Γ(incidenceKernelSheaf K, U) :=
  (incidenceSchemeSection_kernel_exists K U s).exists.choose

lemma incidenceSchemeToKernelSection_coefficients (U : (grassmannianScheme K 3 3).Opens)
    (s : IncidenceSchemeSections K U) :
    (incidenceKernelSheafι K).val.app (op U) (incidenceSchemeToKernelSection K U s) =
      incidenceSchemeSectionCoefficients K U s :=
  (incidenceSchemeSection_kernel_exists K U s).exists.choose_spec

lemma incidenceSchemeToKernelSection_injective (U : (grassmannianScheme K 3 3).Opens) :
    Function.Injective (incidenceSchemeToKernelSection K U) := by
  intro s t h
  apply incidenceSchemeSectionCoefficients_injective K U
  exact (incidenceSchemeToKernelSection_coefficients K U s).symm.trans
    ((congrArg ((incidenceKernelSheafι K).val.app (op U)) h).trans
      (incidenceSchemeToKernelSection_coefficients K U t))

end
end PfaffianDescent
