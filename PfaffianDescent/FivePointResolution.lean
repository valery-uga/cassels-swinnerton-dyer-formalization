import PfaffianDescent.FrameIdealNormalization
import PfaffianDescent.LinearFrameResolution
import PfaffianDescent.FrameMinimality

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K : Type*} [Field K]

/-- The five displayed quadratic generators are linearly independent. -/
theorem frameRelations_independent : LinearIndependent K (frameRelations (K := K)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let v : Fin 5 → FrameHomogeneous K 0 := fun j =>
    ⟨C (c j), isHomogeneous_C _ _⟩
  have hv : frameGradedLast 0 v = 0 := by
    apply Subtype.ext
    change (∑ j, C (c j) * frameRelations j) = 0
    simpa only [MvPolynomial.smul_eq_C_mul] using hc
  have hmem : v ∈ LinearMap.ker (frameGradedLast 0) := hv
  rw [frameGradedLast_ker_zero, Submodule.mem_bot] at hmem
  have he := congrArg (fun w : Fin 5 → FrameHomogeneous K 0 => (w i).val) hmem
  change C (c i) = 0 at he
  exact MvPolynomial.C_injective (Fin 4) K (he.trans (map_zero MvPolynomial.C).symm)

/-- An arbitrary projective frame has the stated minimal graded free resolution.
The ideal is defined from the actual homogeneous prime ideals of its points. -/
theorem five_point_free_resolution (p : Fin 5 → (Fin 4 → K)) (hp : FivePointGeneralPosition p) :
    ∃ E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K,
      (∀ d (f : MvPolynomial (Fin 4) K), f.IsHomogeneous d → (E f).IsHomogeneous d) ∧
      Function.Injective (changedFrameFirst E) ∧
      LinearMap.range (changedFrameFirst E) = LinearMap.ker (changedFrameMiddle E) ∧
      LinearMap.range (changedFrameMiddle E) = LinearMap.ker (changedFrameLast E) ∧
      LinearMap.range (changedFrameLast E) = fiveVectorIdeal p ∧
      (∀ i : Fin 5, (E (frameRelations i)).IsHomogeneous 2) ∧
      (∀ i j : Fin 5, (E (frameMatrix X i j)).IsHomogeneous 1) ∧
      IsAlternating ((frameMatrix X).map E) := by
  obtain ⟨E, hE, hI⟩ := fiveVectorIdeal_normalization p hp
  obtain ⟨hi, hfirst, hmiddle⟩ := changed_frame_resolution E
  refine ⟨E, hE, hi, hfirst, hmiddle, (changedFrameLast_range E).trans hI, ?_, ?_,
    changedFrameMatrix_alternating E⟩
  · intro i; exact hE 2 _ (frameRelations_homogeneous i)
  · intro i j; exact hE 1 _ (frameMatrix_homogeneous i j)

/-- The augmentation step for every degree-preserving polynomial coordinate isomorphism. -/
theorem changed_frame_cubic_augmentation
    (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)
    (hE : ∀ d (g : MvPolynomial (Fin 4) K), g.IsHomogeneous d → (E g).IsHomogeneous d)
    (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (hI : f ∈ (frameIdeal (K := K)).map E.toRingHom) :
    ∃ l : Fin 5 → MvPolynomial (Fin 4) K, (∀ i, (l i).IsHomogeneous 1) ∧
      pf6 (frameAugmentedMatrix (fun i => E (X i)) l) = f := by
  rw [← changedFrameLast_range] at hI
  obtain ⟨v, hv⟩ := hI
  let l := fun i : Fin 5 => homogeneousComponent 1 (v i)
  refine ⟨l, fun i => homogeneousComponent_isHomogeneous 1 (v i), ?_⟩
  rw [frameAugmentedMatrix_pfaffian, frameQuadrics_map]
  have he : homogeneousComponent 3 (changedFrameLast E v) =
      ∑ i, homogeneousComponent 1 (v i) * E (frameRelations i) := by
    change homogeneousComponent 3 (∑ i, v i * E (frameRelations i)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact homogeneousComponent_mul_right (hE 2 _ (frameRelations_homogeneous i)) 1
  rw [← he, hv, homogeneousComponent_eq_self hf]

/-- Every cubic through a projective frame is the Pfaffian of its augmented
resolution matrix, with linear coordinates and linear augmentation entries. -/
theorem five_point_frame_cubic_augmentation (p : Fin 5 → (Fin 4 → K))
    (hp : FivePointGeneralPosition p) (f : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3) (hI : f ∈ fiveVectorIdeal p) :
    ∃ x : Fin 4 → MvPolynomial (Fin 4) K,
      ∃ l : Fin 5 → MvPolynomial (Fin 4) K,
        (∀ i, (x i).IsHomogeneous 1) ∧ (∀ i, (l i).IsHomogeneous 1) ∧
        IsAlternating (frameAugmentedMatrix x l) ∧ pf6 (frameAugmentedMatrix x l) = f := by
  obtain ⟨E, hE, he⟩ := fiveVectorIdeal_normalization p hp
  rw [← he] at hI
  obtain ⟨l, hl, hpf⟩ := changed_frame_cubic_augmentation E hE f hf hI
  exact ⟨fun i => E (X i), l, fun i => hE 1 _ (isHomogeneous_X K i), hl,
    frameAugmentedMatrix_alternating _ _, hpf⟩

end
end PfaffianDescent
