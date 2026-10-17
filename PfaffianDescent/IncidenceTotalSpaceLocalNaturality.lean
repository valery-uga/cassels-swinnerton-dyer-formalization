import PfaffianDescent.IncidenceTotalSpaceCoefficients

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
section
variable (K : Type u) [CommRing K]

lemma incidenceKernelSheafι_sections_injective (U : (grassmannianScheme K 3 3).Opens) :
    Function.Injective ((incidenceKernelSheafι K).val.app (op U)) := by
  intro x y h
  apply (incidenceKernelSheafSectionsEquiv K U).injective
  apply Subtype.ext
  exact (incidenceKernelSheafSectionsEquiv_val K U x).trans
    (h.trans (incidenceKernelSheafSectionsEquiv_val K U y).symm)

/-- Restriction of an actual kernel-sheaf section. -/
noncomputable def incidenceKernelSectionRestrict
    (U V : (grassmannianScheme K 3 3).Opens) (h : V ≤ U)
    (x : Γ(incidenceKernelSheaf K, U)) : Γ(incidenceKernelSheaf K, V) :=
  (incidenceKernelSheaf K).val.map (homOfLE h).op x

lemma incidenceKernelSectionRestrict_coefficients
    (U V : (grassmannianScheme K 3 3).Opens) (h : V ≤ U) (x : Γ(incidenceKernelSheaf K, U)) :
    (incidenceKernelSheafι K).val.app (op V) (incidenceKernelSectionRestrict K U V h x) =
      regularFunctionRestrictFrom (grassmannianScheme K 3 3) U V h ∘
        ((incidenceKernelSheafι K).val.app (op U) x) :=
  PresheafOfModules.naturality_apply (incidenceKernelSheafι K).val (homOfLE h).op x

/-- The local total-space identification is independent of the selected Grassmannian chart. -/
theorem incidenceSchemeKernelSectionsOnChart_independent
    (σ τ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (U : (grassmannianScheme K 3 3).Opens)
    (hσ : U ≤ (grassmannianChartι K σ).opensRange) (hτ : U ≤ (grassmannianChartι K τ).opensRange)
    (s : IncidenceSchemeSections K U) :
    incidenceSchemeKernelSectionsOnChart K σ U hσ s = incidenceSchemeKernelSectionsOnChart K τ U hτ s := by
  apply incidenceKernelSheafι_sections_injective K U
  exact (incidenceSchemeKernelSectionsOnChart_coefficients K σ U hσ s).trans
    (incidenceSchemeKernelSectionsOnChart_coefficients K τ U hτ s).symm

/-- The local total-space identification commutes with restriction of sections. -/
theorem incidenceSchemeKernelSectionsOnChart_restrict
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (U V : (grassmannianScheme K 3 3).Opens)
    (hU : U ≤ (grassmannianChartι K σ).opensRange) (hV : V ≤ U)
    (s : IncidenceSchemeSections K U) :
    incidenceSchemeKernelSectionsOnChart K σ V (hV.trans hU)
        (incidenceSchemeSectionsRestrict K U V hV s) =
      incidenceKernelSectionRestrict K U V hV (incidenceSchemeKernelSectionsOnChart K σ U hU s) := by
  apply incidenceKernelSheafι_sections_injective K V
  exact (incidenceSchemeKernelSectionsOnChart_coefficients K σ V (hV.trans hU) _).trans
    ((incidenceSchemeSectionCoefficients_restrict K U V hV s).trans
      ((congrArg (fun c => regularFunctionRestrictFrom (grassmannianScheme K 3 3) U V hV ∘ c)
        (incidenceSchemeKernelSectionsOnChart_coefficients K σ U hU s).symm).trans
        (incidenceKernelSectionRestrict_coefficients K U V hV _).symm))

end
end PfaffianDescent
