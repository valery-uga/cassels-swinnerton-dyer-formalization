import PfaffianDescent.IncidenceAmbientCoordinates

namespace PfaffianDescent
open Module
section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The free-coordinate evaluations, defined even for a form not isotropic on the graph. -/
noncomputable def incidenceRawKernelCoordinates
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) : IncidenceKernelIndex → R
  | Sum.inl (i, j) => B ![(Pi.single i 1, f (Pi.single i 1)), (0, Pi.single j 1)]
  | Sum.inr s => B ![(0, Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s 0) 1),
      (0, Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s 1) 1)]

lemma incidenceRawKernelCoordinates_eq
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (B : LinearMap.ker (alternatingRestriction R ((Fin 3 → R) × (Fin 3 → R)) f.graph)) :
    incidenceRawKernelCoordinates f B.1 = incidenceGraphKernelCoordinates f B := by
  funext s
  rcases s with ⟨i, j⟩ | s
  · exact (incidenceGraphKernelCoordinates_inl f B i j).symm
  · exact (incidenceGraphKernelCoordinates_inr_pair f B s).symm

lemma incidenceRawKernelCoordinates_map (φ : R →+* S)
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) (g : (Fin 3 → S) →ₗ[S] (Fin 3 → S))
    (hfg : ∀ x, g (φ ∘ x) = φ ∘ f x)
    (B : AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)))
    (C : AlternatingTwoForms S ((Fin 3 → S) × (Fin 3 → S)))
    (hBC : ∀ x y : (Fin 3 → R) × (Fin 3 → R),
      C ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] = φ (B ![x, y])) :
    incidenceRawKernelCoordinates g C = φ ∘ incidenceRawKernelCoordinates f B := by
  funext s
  rcases s with ⟨i, j⟩ | s
  · have h := hBC (Pi.single i 1, f (Pi.single i 1)) (0, Pi.single j 1)
    have hf := hfg (Pi.single i 1)
    rw [ringHom_comp_single_one] at hf
    simpa only [incidenceRawKernelCoordinates, Function.comp_apply, Prod.fst, Prod.snd,
      ringHom_comp_single_one, ringHom_comp_zero, ← hf] using h
  · have h := hBC (0, Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s 0) 1)
      (0, Pi.single (Set.powersetCard.ofFinEmbEquiv.symm s 1) 1)
    simpa only [incidenceRawKernelCoordinates, Function.comp_apply, Prod.fst, Prod.snd,
      ringHom_comp_single_one, ringHom_comp_zero] using h

lemma incidenceAmbientBasis_coord_map (φ : R →+* S) (i : Fin 6)
    (x : (Fin 3 → R) × (Fin 3 → R)) :
    (incidenceAmbientBasis S).coord i (φ ∘ x.1, φ ∘ x.2) =
      φ ((incidenceAmbientBasis R).coord i x) := by
  simp only [Basis.coord_apply, incidenceAmbientBasis, Basis.repr_reindex_apply]
  rcases (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).symm i with j | j <;> rfl

/-- Reconstructing an arbitrary ambient form from its fifteen coefficients commutes with ring maps. -/
lemma incidenceAmbientCoordinates_symm_map (φ : R →+* S)
    (c : Set.powersetCard (Fin 6) 2 → R) (x y : (Fin 3 → R) × (Fin 3 → R)) :
    (alternatingCoordinates (incidenceAmbientBasis S)).symm (φ ∘ c)
      ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] =
      φ ((alternatingCoordinates (incidenceAmbientBasis R)).symm c ![x, y]) := by
  rw [alternatingCoordinates_symm_evaluation, alternatingCoordinates_symm_evaluation, map_sum]
  apply Finset.sum_congr rfl
  intro s _
  rw [map_mul, RingHom.map_det]
  congr 1
  apply congrArg Matrix.det
  ext i j
  fin_cases i <;> exact incidenceAmbientBasis_coord_map φ _ _

/-- Recover local graph and fiber coordinates from a graph and three original ambient forms. -/
noncomputable def incidenceRecoverCoordinates (i : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R))
    (B : Fin 3 → AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R))) : IncidenceGraphIndex → R
  | Sum.inl (a, b) => LinearMap.toMatrix' f a b
  | Sum.inr (k, s) => incidenceRawKernelCoordinates f
      (alternatingTransport (graphCoordinatePermutation R i) (B k)) s

lemma incidenceRecoverCoordinates_actual (i : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (p : IncidenceGraphPoints R) :
    incidenceRecoverCoordinates i p.1 (incidenceOriginalForm i p) =
      incidenceGraphPointCoordinates R p := by
  funext s
  rcases s with ⟨a, b⟩ | ⟨k, s⟩
  · rfl
  · change incidenceRawKernelCoordinates p.1
      (alternatingTransport (graphCoordinatePermutation R i) (incidenceOriginalForm i p k)) s = _
    have he : alternatingTransport (graphCoordinatePermutation R i) (incidenceOriginalForm i p k) =
        (p.2 k).1 := by
      unfold incidenceOriginalForm
      rw [← graphCoordinatePermutation_symm]
      exact (alternatingTransport (graphCoordinatePermutation R i)).apply_symm_apply _
    rw [he, incidenceRawKernelCoordinates_eq]
    rfl

lemma incidenceRecoverCoordinates_map (φ : R →+* S)
    (i : Equiv.Perm (Fin 3 ⊕ Fin 3))
    (f : (Fin 3 → R) →ₗ[R] (Fin 3 → R)) (g : (Fin 3 → S) →ₗ[S] (Fin 3 → S))
    (hfg : ∀ x, g (φ ∘ x) = φ ∘ f x)
    (B : Fin 3 → AlternatingTwoForms R ((Fin 3 → R) × (Fin 3 → R)))
    (C : Fin 3 → AlternatingTwoForms S ((Fin 3 → S) × (Fin 3 → S)))
    (hBC : ∀ k (x y : (Fin 3 → R) × (Fin 3 → R)),
      C k ![(φ ∘ x.1, φ ∘ x.2), (φ ∘ y.1, φ ∘ y.2)] = φ (B k ![x, y])) :
    incidenceRecoverCoordinates i g C = φ ∘ incidenceRecoverCoordinates i f B := by
  funext s
  rcases s with ⟨a, b⟩ | ⟨k, s⟩
  · have h := hfg (Pi.single b 1)
    rw [ringHom_comp_single_one] at h
    exact congrFun h a
  · exact congrFun (incidenceRawKernelCoordinates_map φ f g hfg _ _
      (alternatingTransport_permutation_map φ i (B k) (C k) (hBC k))) s

end
end PfaffianDescent
