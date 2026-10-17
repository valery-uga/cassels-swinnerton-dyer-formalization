import PfaffianDescent.IncidenceOpenChartEquations

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R]
    (σ τ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T S : Matrix (Fin 3) (Fin 3) R)
    (hW : grassmannianChartSubmodule R σ T = grassmannianChartSubmodule R τ S)
include hW

lemma incidenceRestrictionKernels_eq :
    (incidenceRestrictionMap R σ T).ker = (incidenceRestrictionMap R τ S).ker := by
  ext c
  exact incidenceRestrictionMap_zero_iff_submodule R σ τ T S hW c

/-- The actual fiber-basis transition through the common ambient coefficient module. -/
noncomputable def incidenceAmbientFiberTransition :
    (IncidenceFiberIndex → R) ≃ₗ[R] (IncidenceFiberIndex → R) :=
  (incidenceRestrictionFiberEquiv R σ T).symm.trans
    ((LinearEquiv.ofEq _ _ (incidenceRestrictionKernels_eq R σ τ T S hW)).trans
      (incidenceRestrictionFiberEquiv R τ S))

lemma incidenceAmbientFiberTransition_apply (c : IncidenceFiberIndex → R) :
    incidenceAmbientFiberTransition R σ τ T S hW c =
      incidenceFiberProjection R τ S (incidenceFiberInclusion R σ T c) := by
  let d := (LinearEquiv.ofEq _ _ (incidenceRestrictionKernels_eq R σ τ T S hW))
    ((incidenceRestrictionFiberEquiv R σ T).symm c)
  exact (incidenceFiberProjection_kernel R τ S d).symm

lemma incidenceAmbientFiberTransition_reconstruct (c : IncidenceFiberIndex → R) :
    incidenceFiberInclusion R τ S (incidenceAmbientFiberTransition R σ τ T S hW c) =
      incidenceFiberInclusion R σ T c := by
  let d := (LinearEquiv.ofEq _ _ (incidenceRestrictionKernels_eq R σ τ T S hW))
    ((incidenceRestrictionFiberEquiv R σ T).symm c)
  exact congrArg Subtype.val ((incidenceRestrictionFiberEquiv R τ S).symm_apply_apply d)

end
section
variable (R : Type*) [CommRing R]
    (σ τ υ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T S Q : Matrix (Fin 3) (Fin 3) R)
    (hTS : grassmannianChartSubmodule R σ T = grassmannianChartSubmodule R τ S)
    (hSQ : grassmannianChartSubmodule R τ S = grassmannianChartSubmodule R υ Q)

/-- The transitions of the actual kernel bases satisfy the cocycle identity. -/
lemma incidenceAmbientFiberTransition_trans :
    (incidenceAmbientFiberTransition R σ τ T S hTS).trans
      (incidenceAmbientFiberTransition R τ υ S Q hSQ) =
      incidenceAmbientFiberTransition R σ υ T Q (hTS.trans hSQ) := by
  apply LinearEquiv.ext
  intro c
  change incidenceAmbientFiberTransition R τ υ S Q hSQ
    (incidenceAmbientFiberTransition R σ τ T S hTS c) = _
  rw [incidenceAmbientFiberTransition_apply, incidenceAmbientFiberTransition_reconstruct,
    incidenceAmbientFiberTransition_apply]

end
section
variable {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    (σ τ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T S : Matrix (Fin 3) (Fin 3) R)
    (hW : grassmannianChartSubmodule R σ T = grassmannianChartSubmodule R τ S)
include hW

lemma incidenceChartSubmodule_eq_map :
    grassmannianChartSubmodule A σ (T.map φ) = grassmannianChartSubmodule A τ (S.map φ) := by
  have he := congrArg (grassmannianSubmoduleBaseChange φ) hW
  simpa only [grassmannianChartSubmodule_baseChange] using he

/-- The actual invertible fiber transitions commute with arbitrary coefficient homomorphisms. -/
lemma incidenceAmbientFiberTransition_map (c : IncidenceFiberIndex → R) :
    incidenceAmbientFiberTransition A σ τ (T.map φ) (S.map φ)
      (incidenceChartSubmodule_eq_map φ σ τ T S hW) (φ ∘ c) =
      φ ∘ incidenceAmbientFiberTransition R σ τ T S hW c := by
  rw [incidenceAmbientFiberTransition_apply, incidenceFiberInclusion_map,
    incidenceFiberProjection_map, incidenceAmbientFiberTransition_apply]

end
end PfaffianDescent
