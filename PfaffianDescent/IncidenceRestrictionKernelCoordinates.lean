import PfaffianDescent.IncidenceRestrictionMatrix
import PfaffianDescent.IncidenceProjectiveKernels

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R]
  (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R)

/-- The matrix kernel is precisely the actual module of ambient isotropic triples. -/
noncomputable def incidenceRestrictionKernelEquiv :
    (incidenceRestrictionMap R σ T).ker ≃ₗ[R]
      IncidenceQuotientFiber R (grassmannianChartQuotient R σ T) where
  toFun c k := ⟨(alternatingCoordinates (incidenceAmbientBasis R)).symm (fun s => c.1 (k, s)),
    (incidenceRestrictionMap_eq_zero_iff R σ T c.1).mp c.2 k⟩
  invFun B := ⟨fun i => alternatingCoordinates (incidenceAmbientBasis R) (B i.1).1 i.2, by
    apply (incidenceRestrictionMap_eq_zero_iff R σ T _).mpr
    intro k
    change alternatingRestriction R _ (grassmannianChartSubmodule R σ T)
      ((alternatingCoordinates (incidenceAmbientBasis R)).symm
        (alternatingCoordinates (incidenceAmbientBasis R) (B k).1)) = 0
    rw [LinearEquiv.symm_apply_apply]
    exact (B k).2⟩
  left_inv c := by
    apply Subtype.ext
    funext i
    exact congrFun ((alternatingCoordinates (incidenceAmbientBasis R)).apply_symm_apply
      (fun s => c.1 (i.1, s))) i.2
  right_inv B := by
    funext k
    apply Subtype.ext
    exact (alternatingCoordinates (incidenceAmbientBasis R)).symm_apply_apply (B k).1
  map_add' c d := by
    funext k
    apply Subtype.ext
    exact (alternatingCoordinates (incidenceAmbientBasis R)).symm.map_add _ _
  map_smul' r c := by
    funext k
    apply Subtype.ext
    exact (alternatingCoordinates (incidenceAmbientBasis R)).symm.map_smul r _

/-- Explicit thirty-six free coordinates on the kernel of the chart restriction matrix. -/
noncomputable def incidenceRestrictionKernelCoordinates :
    (incidenceRestrictionMap R σ T).ker ≃ₗ[R] (Fin 3 → IncidenceKernelIndex → R) :=
  (incidenceRestrictionKernelEquiv R σ T).trans (grassmannianChartFiberCoordinates R σ T)

instance incidenceRestrictionKernel_free : Module.Free R (incidenceRestrictionMap R σ T).ker :=
  Module.Free.of_equiv (incidenceRestrictionKernelCoordinates R σ T).symm

lemma incidenceRestrictionKernel_rank [Nontrivial R] :
    Module.finrank R (incidenceRestrictionMap R σ T).ker = 36 := by
  rw [(incidenceRestrictionKernelCoordinates R σ T).finrank_eq, Module.finrank_pi_fintype]
  simp [Module.finrank_pi, incidenceKernelIndex_card]

end
end PfaffianDescent
