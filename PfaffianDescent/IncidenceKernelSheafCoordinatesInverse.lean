import PfaffianDescent.IncidenceKernelSheafLocalFree

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Opposite
universe u
section
variable (K : Type u) [CommRing K] (σ : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (U : (grassmannianScheme K 3 3).Opens) (hU : U ≤ (grassmannianChartι K σ).opensRange)

/-- Reconstructing a sheaf section from its chart coordinates gives the actual ambient fiber inclusion. -/
lemma incidenceKernelSheafOpenSectionsEquiv_symm_val
    (c : IncidenceFiberIndex → Γ(grassmannianScheme K 3 3, U)) :
    (incidenceKernelSheafι K).val.app (op U) ((incidenceKernelSheafOpenSectionsEquiv K σ U hU).symm c) =
      incidenceFiberInclusion _ σ (incidenceOpenChartMatrix K σ U hU) c := by
  let d := (LinearEquiv.ofEq _ _ (incidenceEquationSections_eq_open_chart K σ U hU)).symm
    ((incidenceRestrictionFiberEquiv _ σ (incidenceOpenChartMatrix K σ U hU)).symm c)
  have h : incidenceKernelSheafSectionsEquiv K U
      ((incidenceKernelSheafOpenSectionsEquiv K σ U hU).symm c) = d :=
    (incidenceKernelSheafSectionsEquiv K U).apply_symm_apply d
  exact (incidenceKernelSheafSectionsEquiv_val K U _).symm.trans (congrArg Subtype.val h)

end
end PfaffianDescent
