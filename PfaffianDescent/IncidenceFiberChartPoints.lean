import PfaffianDescent.IncidenceAmbientFiberTransition
import PfaffianDescent.IncidenceSchemeIsotropy

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R] (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (p : IncidenceGraphPoints R)

/-- The kernel-sheaf projection recovers exactly the fiber coordinates of an actual incidence chart point. -/
lemma incidenceFiberProjection_original :
    incidenceFiberProjection R σ (LinearMap.toMatrix' p.1) (incidenceOriginalCoefficients σ p) =
      (fun i : IncidenceFiberIndex => incidenceGraphPointCoordinates R p (Sum.inr i)) := by
  funext i
  change incidenceRawKernelCoordinates (Matrix.toLin' (LinearMap.toMatrix' p.1))
    (alternatingTransport (graphCoordinatePermutation R σ)
      ((alternatingCoordinates (incidenceAmbientBasis R)).symm
        (alternatingCoordinates (incidenceAmbientBasis R) (incidenceOriginalForm σ p i.1)))) i.2 = _
  rw [LinearEquiv.symm_apply_apply, Matrix.toLin'_toMatrix']
  exact congrFun (incidenceRecoverCoordinates_actual σ p) (Sum.inr i)

lemma incidenceOriginalCoefficients_isotropic :
    incidenceRestrictionMap R σ (LinearMap.toMatrix' p.1) (incidenceOriginalCoefficients σ p) = 0 := by
  apply (incidenceRestrictionMap_eq_zero_iff R σ (LinearMap.toMatrix' p.1) _).mpr
  intro k
  change alternatingRestriction R _ (grassmannianChartSubmodule R σ (LinearMap.toMatrix' p.1))
    ((alternatingCoordinates (incidenceAmbientBasis R)).symm
      (alternatingCoordinates (incidenceAmbientBasis R) (incidenceOriginalForm σ p k))) = 0
  rw [LinearEquiv.symm_apply_apply]
  exact incidenceOriginalForm_restriction_zero σ p k

/-- The kernel-sheaf reconstruction gives exactly the actual ambient forms carried by the incidence scheme. -/
lemma incidenceFiberInclusion_original :
    incidenceFiberInclusion R σ (LinearMap.toMatrix' p.1)
      (fun i : IncidenceFiberIndex => incidenceGraphPointCoordinates R p (Sum.inr i)) =
      incidenceOriginalCoefficients σ p := by
  rw [← incidenceFiberProjection_original R σ p]
  exact incidenceFiberInclusion_projection R σ (LinearMap.toMatrix' p.1)
    (incidenceOriginalCoefficients σ p) (incidenceOriginalCoefficients_isotropic R σ p)

end
end PfaffianDescent
