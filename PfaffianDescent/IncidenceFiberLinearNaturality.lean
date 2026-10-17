import PfaffianDescent.IncidenceFiberLinearMaps

namespace PfaffianDescent
section
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R)

/-- The ambient projection onto fiber coordinates commutes with arbitrary ring maps. -/
lemma incidenceFiberProjection_map (c : AlternatingTripleIndex → R) :
    incidenceFiberProjection S σ (T.map φ) (φ ∘ c) = φ ∘ incidenceFiberProjection R σ T c := by
  funext i
  have hf : ∀ x, Matrix.toLin' (T.map φ) (φ ∘ x) = φ ∘ Matrix.toLin' T x := by
    intro x
    funext j
    exact (RingHom.map_mulVec φ T x j).symm
  exact congrFun (incidenceRawKernelCoordinates_map φ (Matrix.toLin' T)
    (Matrix.toLin' (T.map φ)) hf _ _
    (alternatingTransport_permutation_map φ σ _ _
      (fun x y => incidenceAmbientCoordinates_symm_map φ (fun s => c (i.1, s)) x y))) i.2

/-- The actual reconstruction of an isotropic triple commutes with arbitrary scalar extension. -/
lemma incidenceFiberInclusion_map (c : IncidenceFiberIndex → R) :
    incidenceFiberInclusion S σ (T.map φ) (φ ∘ c) = φ ∘ incidenceFiberInclusion R σ T c := by
  let d := incidenceFiberInclusion R σ T c
  have hd : incidenceRestrictionMap S σ (T.map φ) (φ ∘ d) = 0 := by
    rw [incidenceRestrictionMap_map, incidenceFiberInclusion_isotropic]
    funext i
    exact map_zero φ
  have hp : incidenceFiberProjection S σ (T.map φ) (φ ∘ d) = φ ∘ c := by
    rw [incidenceFiberProjection_map, incidenceFiberProjection_inclusion]
  exact (congrArg (incidenceFiberInclusion S σ (T.map φ)) hp.symm).trans
    (incidenceFiberInclusion_projection S σ (T.map φ) (φ ∘ d) hd)

end
section
variable (R : Type*) [CommRing R]
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R)

noncomputable def incidenceFiberProjectionMatrix : Matrix IncidenceFiberIndex AlternatingTripleIndex R := by
  classical
  exact LinearMap.toMatrix' (incidenceFiberProjection R σ T)

noncomputable def incidenceFiberInclusionMatrix : Matrix AlternatingTripleIndex IncidenceFiberIndex R := by
  classical
  exact LinearMap.toMatrix' (incidenceFiberInclusion R σ T)

lemma incidenceFiberProjectionMatrix_toLin :
    Matrix.toLin' (incidenceFiberProjectionMatrix R σ T) = incidenceFiberProjection R σ T := by
  classical
  exact Matrix.toLin'_toMatrix' _

lemma incidenceFiberInclusionMatrix_toLin :
    Matrix.toLin' (incidenceFiberInclusionMatrix R σ T) = incidenceFiberInclusion R σ T := by
  classical
  exact Matrix.toLin'_toMatrix' _

end
section
variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (σ : Equiv.Perm (Fin 3 ⊕ Fin 3)) (T : Matrix (Fin 3) (Fin 3) R)

lemma incidenceFiberProjectionMatrix_map :
    (incidenceFiberProjectionMatrix R σ T).map φ = incidenceFiberProjectionMatrix S σ (T.map φ) := by
  classical
  funext i j
  change φ (incidenceFiberProjection R σ T (Pi.single j 1) i) =
    incidenceFiberProjection S σ (T.map φ) (Pi.single j 1) i
  have h := congrFun (incidenceFiberProjection_map φ σ T (Pi.single j 1)) i
  have he : φ ∘ Pi.single j (1 : R) = Pi.single j (1 : S) := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  rw [he] at h
  exact h.symm

lemma incidenceFiberInclusionMatrix_map :
    (incidenceFiberInclusionMatrix R σ T).map φ = incidenceFiberInclusionMatrix S σ (T.map φ) := by
  classical
  funext i j
  change φ (incidenceFiberInclusion R σ T (Pi.single j 1) i) =
    incidenceFiberInclusion S σ (T.map φ) (Pi.single j 1) i
  have h := congrFun (incidenceFiberInclusion_map φ σ T (Pi.single j 1)) i
  have he : φ ∘ Pi.single j (1 : R) = Pi.single j (1 : S) := by
    funext k
    by_cases hk : k = j <;> simp [hk]
  rw [he] at h
  exact h.symm

end
end PfaffianDescent
