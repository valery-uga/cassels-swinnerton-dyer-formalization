import PfaffianDescent.IncidenceRestrictionKernelCoordinates
import PfaffianDescent.IncidenceCoordinateRecovery
import PfaffianDescent.IncidenceChartProduct

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R]

/-- Evaluation of the twelve graph coordinates is linear on all ambient forms. -/
noncomputable def incidenceRawKernelLinearMap
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) :
    AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)) →ₗ[R] (IncidenceKernelIndex → R) where
  toFun := incidenceRawKernelCoordinates f
  map_add' B C := by
    funext s
    cases s <;> rfl
  map_smul' r B := by
    funext s
    cases s <;> rfl

/-- Flatten the three sets of twelve coordinates into the thirty-six fiber coordinates. -/
def incidenceFiberFlatten : (Fin 3 → IncidenceKernelIndex → R) ≃ₗ[R] (IncidenceFiberIndex → R) where
  toFun c i := c i.1 i.2
  invFun c k s := c (k, s)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R)

/-- The actual matrix kernel with its thirty-six ordered coordinates. -/
noncomputable def incidenceRestrictionFiberEquiv :
    (incidenceRestrictionMap R σ T).ker ≃ₗ[R] (IncidenceFiberIndex → R) :=
  (incidenceRestrictionKernelCoordinates R σ T).trans (incidenceFiberFlatten R)

/-- Extend the free-coordinate projection to all forty-five ambient coefficients. -/
noncomputable def incidenceFiberProjection :
    (AlternatingTripleIndex → R) →ₗ[R] (IncidenceFiberIndex → R) where
  toFun c i := incidenceRawKernelCoordinates (Matrix.toLin' T)
    (alternatingTransport (graphCoordinatePermutation R σ)
      ((alternatingCoordinates (incidenceAmbientBasis R)).symm (fun s => c (i.1, s)))) i.2
  map_add' c d := by
    change (fun i : IncidenceFiberIndex => ((incidenceRawKernelLinearMap R (Matrix.toLin' T)).comp
      ((alternatingTransport (graphCoordinatePermutation R σ)).toLinearMap.comp
        (alternatingCoordinates (incidenceAmbientBasis R)).symm.toLinearMap))
        ((fun s => c (i.1, s)) + (fun s => d (i.1, s))) i.2) = _
    simp only [map_add, Pi.add_apply]
    rfl
  map_smul' r c := by
    change (fun i : IncidenceFiberIndex => ((incidenceRawKernelLinearMap R (Matrix.toLin' T)).comp
      ((alternatingTransport (graphCoordinatePermutation R σ)).toLinearMap.comp
        (alternatingCoordinates (incidenceAmbientBasis R)).symm.toLinearMap))
        (r • (fun s => c (i.1, s))) i.2) = _
    simp only [map_smul, Pi.smul_apply]
    rfl

lemma incidenceFiberProjection_kernel (c : (incidenceRestrictionMap R σ T).ker) :
    incidenceFiberProjection R σ T c.1 = incidenceRestrictionFiberEquiv R σ T c := by
  funext i
  let B := (incidenceRestrictionKernelEquiv R σ T c) i.1
  let D := (alternatingKernelTransportEquiv (graphCoordinatePermutation R σ.symm)
    (Matrix.toLin' T).graph (grassmannianChartSubmodule R σ T) rfl).symm B
  have h := congrFun (incidenceRawKernelCoordinates_eq (Matrix.toLin' T) D) i.2
  have he : D.1 = alternatingTransport (graphCoordinatePermutation R σ) B.1 := by
    change alternatingTransport (graphCoordinatePermutation R σ.symm).symm B.1 = _
    rw [graphCoordinatePermutation_symm, Equiv.symm_symm]
  change incidenceRawKernelCoordinates (Matrix.toLin' T)
    (alternatingTransport (graphCoordinatePermutation R σ) B.1) i.2 = _
  exact (congrArg (fun b => incidenceRawKernelCoordinates (Matrix.toLin' T) b i.2) he.symm).trans h

/-- Reconstruct ambient coefficients from arbitrary thirty-six fiber coordinates. -/
noncomputable def incidenceFiberInclusion :
    (IncidenceFiberIndex → R) →ₗ[R] (AlternatingTripleIndex → R) :=
  (incidenceRestrictionMap R σ T).ker.subtype.comp
    (incidenceRestrictionFiberEquiv R σ T).symm.toLinearMap

lemma incidenceFiberProjection_inclusion (c : IncidenceFiberIndex → R) :
    incidenceFiberProjection R σ T (incidenceFiberInclusion R σ T c) = c :=
  (incidenceFiberProjection_kernel R σ T ((incidenceRestrictionFiberEquiv R σ T).symm c)).trans
    ((incidenceRestrictionFiberEquiv R σ T).apply_symm_apply c)

lemma incidenceFiberInclusion_projection (c : AlternatingTripleIndex → R)
    (hc : incidenceRestrictionMap R σ T c = 0) :
    incidenceFiberInclusion R σ T (incidenceFiberProjection R σ T c) = c := by
  have he := incidenceFiberProjection_kernel R σ T ⟨c, hc⟩
  rw [he]
  exact congrArg Subtype.val ((incidenceRestrictionFiberEquiv R σ T).symm_apply_apply ⟨c, hc⟩)

lemma incidenceFiberInclusion_isotropic (c : IncidenceFiberIndex → R) :
    incidenceRestrictionMap R σ T (incidenceFiberInclusion R σ T c) = 0 :=
  ((incidenceRestrictionFiberEquiv R σ T).symm c).2

end
end PfaffianDescent
