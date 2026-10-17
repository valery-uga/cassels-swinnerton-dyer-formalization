import PfaffianDescent.IncidenceTotalSpaceGlobalSections

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
section
variable (K : Type u) [CommRing K]

lemma incidenceSchemeKernelSectionsOnChart_symm_coefficients
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (U : (grassmannianScheme K 3 3).Opens)
    (hU : U ≤ (grassmannianChartι K σ).opensRange) (x : Γ(incidenceKernelSheaf K, U)) :
    incidenceSchemeSectionCoefficients K U ((incidenceSchemeKernelSectionsOnChart K σ U hU).symm x) =
      (incidenceKernelSheafι K).val.app (op U) x :=
  (incidenceSchemeKernelSectionsOnChart_coefficients K σ U hU _).symm.trans
    (congrArg ((incidenceKernelSheafι K).val.app (op U))
      ((incidenceSchemeKernelSectionsOnChart K σ U hU).apply_symm_apply x))

/-- Every global section of the kernel sheaf is represented by an actual incidence scheme section. -/
theorem incidenceSchemeToKernelSection_surjective (U : (grassmannianScheme K 3 3).Opens) :
    Function.Surjective (incidenceSchemeToKernelSection K U) := by
  intro x
  let V := incidenceSectionChartOpen K U
  let hV := incidenceSectionChartOpen_le K U
  let hc := incidenceSectionChartOpen_chart K U
  let t := fun σ => (incidenceSchemeKernelSectionsOnChart K σ (V σ) (hc σ)).symm
    (incidenceKernelSectionRestrict K U (V σ) (hV σ) x)
  have ht : ∀ σ τ, incidenceSchemeSectionsRestrict K (V σ) (V σ ⊓ V τ) inf_le_left (t σ) =
      incidenceSchemeSectionsRestrict K (V τ) (V σ ⊓ V τ) inf_le_right (t τ) := by
    intro σ τ
    apply incidenceSchemeSectionCoefficients_injective K (V σ ⊓ V τ)
    have hi (i : Equiv.Perm (Fin 3 ⊕ Fin 3)) (W : (grassmannianScheme K 3 3).Opens)
        (hW : W ≤ V i) :
        incidenceSchemeSectionCoefficients K W (incidenceSchemeSectionsRestrict K (V i) W hW (t i)) =
          (incidenceKernelSheafι K).val.app (op W)
            (incidenceKernelSectionRestrict K U W (hW.trans (hV i)) x) := by
      exact (incidenceSchemeSectionCoefficients_restrict K (V i) W hW (t i)).trans
        ((congrArg (fun c => regularFunctionRestrictFrom (grassmannianScheme K 3 3) (V i) W hW ∘ c)
          (incidenceSchemeKernelSectionsOnChart_symm_coefficients K i (V i) (hc i) _)).trans
          ((incidenceKernelSectionRestrict_coefficients K (V i) W hW _).symm.trans
            (congrArg ((incidenceKernelSheafι K).val.app (op W))
              (incidenceKernelSectionRestrict_trans K U (V i) W (hV i) hW x))))
    exact (hi σ _ inf_le_left).trans (hi τ _ inf_le_right).symm
  obtain ⟨s, hs, _⟩ := incidenceSchemeSections_glue K U V hV (incidenceSectionChartOpen_cover K U) t ht
  refine ⟨s, ?_⟩
  apply incidenceKernelSheafι_sections_injective K U
  rw [incidenceSchemeToKernelSection_coefficients]
  apply schemeModuleSections_ext (coordinateModuleSheaf (grassmannianScheme K 3 3) AlternatingTripleIndex)
    U V hV (incidenceSectionChartOpen_cover K U)
  intro σ
  change regularFunctionRestrictFrom (grassmannianScheme K 3 3) U (V σ) (hV σ) ∘
      incidenceSchemeSectionCoefficients K U s =
    regularFunctionRestrictFrom (grassmannianScheme K 3 3) U (V σ) (hV σ) ∘
      ((incidenceKernelSheafι K).val.app (op U) x)
  exact (incidenceSchemeSectionCoefficients_restrict K U (V σ) (hV σ) s).symm.trans
    ((congrArg (incidenceSchemeSectionCoefficients K (V σ)) (hs σ)).trans
      ((incidenceSchemeKernelSectionsOnChart_symm_coefficients K σ (V σ) (hc σ) _).trans
        (incidenceKernelSectionRestrict_coefficients K U (V σ) (hV σ) x)))

/-- On every open of the Grassmannian, the actual incidence scheme represents the global rank-36 kernel sheaf. -/
noncomputable def incidenceSchemeKernelSectionsEquiv (U : (grassmannianScheme K 3 3).Opens) :
    IncidenceSchemeSections K U ≃ Γ(incidenceKernelSheaf K, U) :=
  Equiv.ofBijective (incidenceSchemeToKernelSection K U)
    ⟨incidenceSchemeToKernelSection_injective K U, incidenceSchemeToKernelSection_surjective K U⟩

lemma incidenceSchemeKernelSectionsEquiv_coefficients (U : (grassmannianScheme K 3 3).Opens)
    (s : IncidenceSchemeSections K U) :
    (incidenceKernelSheafι K).val.app (op U) (incidenceSchemeKernelSectionsEquiv K U s) =
      incidenceSchemeSectionCoefficients K U s := incidenceSchemeToKernelSection_coefficients K U s

/-- The global representation commutes with restriction to any smaller open. -/
theorem incidenceSchemeKernelSectionsEquiv_restrict
    (U V : (grassmannianScheme K 3 3).Opens) (h : V ≤ U) (s : IncidenceSchemeSections K U) :
    incidenceSchemeKernelSectionsEquiv K V (incidenceSchemeSectionsRestrict K U V h s) =
      incidenceKernelSectionRestrict K U V h (incidenceSchemeKernelSectionsEquiv K U s) := by
  apply incidenceKernelSheafι_sections_injective K V
  exact (incidenceSchemeKernelSectionsEquiv_coefficients K V _).trans
    ((incidenceSchemeSectionCoefficients_restrict K U V h s).trans
      ((congrArg (fun c => regularFunctionRestrictFrom (grassmannianScheme K 3 3) U V h ∘ c)
        (incidenceSchemeKernelSectionsEquiv_coefficients K U s).symm).trans
          (incidenceKernelSectionRestrict_coefficients K U V h _).symm))

/-- On every chart open, the global representation recovers the explicit affine-space trivialization. -/
theorem incidenceSchemeKernelSectionsEquiv_onChart
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (U : (grassmannianScheme K 3 3).Opens)
    (hU : U ≤ (grassmannianChartι K σ).opensRange) (s : IncidenceSchemeSections K U) :
    incidenceSchemeKernelSectionsEquiv K U s = incidenceSchemeKernelSectionsOnChart K σ U hU s := by
  apply incidenceKernelSheafι_sections_injective K U
  exact (incidenceSchemeKernelSectionsEquiv_coefficients K U s).trans
    (incidenceSchemeKernelSectionsOnChart_coefficients K σ U hU s).symm

end
end PfaffianDescent
