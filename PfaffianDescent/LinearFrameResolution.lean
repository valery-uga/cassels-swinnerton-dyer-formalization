import PfaffianDescent.FrameResolutionTransport

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K : Type*} [Field K]

variable (E : MvPolynomial (Fin 4) K ≃ₐ[K] MvPolynomial (Fin 4) K)

lemma changedFrameLast_range : LinearMap.range (changedFrameLast E) =
    (frameIdeal (K := K)).map E.toRingHom := by
  rw [changedFrameLast, Fintype.range_linearCombination, frameIdeal, Ideal.map_span,
    ← Set.range_comp]
  rfl

noncomputable def changedFrameQuotientEquiv : FrameCoordinateRing K ≃ₐ[K]
    (MvPolynomial (Fin 4) K ⧸ (frameIdeal (K := K)).map E.toRingHom) :=
  Ideal.quotientEquivAlg (frameIdeal (K := K)) ((frameIdeal (K := K)).map E.toRingHom) E rfl

lemma frameQuadrics_map : frameQuadrics (fun i : Fin 4 => E (X i)) =
    (fun i => E (frameRelations (K := K) i)) := by
  funext i
  fin_cases i
  · change E (X 0) * E (X 2) - E (X 0) * E (X 1) = E (X 0 * X 2 - X 0 * X 1)
    simp only [map_sub, map_mul]
  · change E (X 0) * E (X 3) - E (X 0) * E (X 1) = E (X 0 * X 3 - X 0 * X 1)
    simp only [map_sub, map_mul]
  · change E (X 1) * E (X 2) - E (X 0) * E (X 1) = E (X 1 * X 2 - X 0 * X 1)
    simp only [map_sub, map_mul]
  · change E (X 1) * E (X 3) - E (X 0) * E (X 1) = E (X 1 * X 3 - X 0 * X 1)
    simp only [map_sub, map_mul]
  · change E (X 2) * E (X 3) - E (X 0) * E (X 1) = E (X 2 * X 3 - X 0 * X 1)
    simp only [map_sub, map_mul]

lemma changedFrameMatrix_alternating : IsAlternating ((frameMatrix X).map E) := by
  constructor
  · intro i
    change E (frameMatrix X i i) = 0
    rw [(frameMatrix_alternating (X : Fin 4 → MvPolynomial (Fin 4) K)).1 i, map_zero]
  · intro i j
    change E (frameMatrix X j i) = -E (frameMatrix X i j)
    rw [(frameMatrix_alternating (X : Fin 4 → MvPolynomial (Fin 4) K)).2 i j, map_neg]

variable (M : Matrix (Fin 4) (Fin 4) K) (hM : IsUnit M.det)

lemma linearFrame_quadrics_homogeneous (i : Fin 5) :
    (linearSubstitutionEquiv M hM (frameRelations i)).IsHomogeneous 2 :=
  linearSubstitution_homogeneous M (frameRelations_homogeneous i)

lemma linearFrame_matrix_homogeneous (i j : Fin 5) :
    (linearSubstitutionEquiv M hM (frameMatrix X i j)).IsHomogeneous 1 :=
  linearSubstitution_homogeneous M (frameMatrix_homogeneous i j)

/-- The exact graded frame resolution after an arbitrary invertible linear coordinate change. -/
theorem linear_frame_resolution :
    let E := linearSubstitutionEquiv M hM
    Function.Injective (changedFrameFirst E) ∧
    LinearMap.range (changedFrameFirst E) = LinearMap.ker (changedFrameMiddle E) ∧
    LinearMap.range (changedFrameMiddle E) = LinearMap.ker (changedFrameLast E) ∧
    LinearMap.range (changedFrameLast E) = (frameIdeal (K := K)).map E.toRingHom ∧
    (∀ i : Fin 5, (E (frameRelations i)).IsHomogeneous 2) ∧
    (∀ i j : Fin 5, (E (frameMatrix X i j)).IsHomogeneous 1) ∧
    IsAlternating ((frameMatrix X).map E) := by
  let E := linearSubstitutionEquiv M hM
  obtain ⟨hi, hfirst, hmiddle⟩ := changed_frame_resolution E
  exact ⟨hi, hfirst, hmiddle, changedFrameLast_range E,
    linearFrame_quadrics_homogeneous M hM, linearFrame_matrix_homogeneous M hM,
    changedFrameMatrix_alternating E⟩

/-- A cubic in the transformed frame ideal is a Pfaffian of the augmented
alternating matrix, with genuinely linear augmentation entries. -/
theorem linear_frame_cubic_augmentation (f : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 3)
    (hI : f ∈ (frameIdeal (K := K)).map (linearSubstitutionEquiv M hM).toRingHom) :
    ∃ l : Fin 5 → MvPolynomial (Fin 4) K, (∀ i, (l i).IsHomogeneous 1) ∧
      pf6 (frameAugmentedMatrix (fun i => linearSubstitutionEquiv M hM (X i)) l) = f := by
  let E := linearSubstitutionEquiv M hM
  obtain ⟨v, hv⟩ : ∃ v, changedFrameLast E v = f := by
    rw [← changedFrameLast_range] at hI
    exact hI
  let l := fun i : Fin 5 => homogeneousComponent 1 (v i)
  refine ⟨l, fun i => homogeneousComponent_isHomogeneous 1 (v i), ?_⟩
  rw [frameAugmentedMatrix_pfaffian, frameQuadrics_map]
  have he : homogeneousComponent 3 (changedFrameLast E v) =
      ∑ i, homogeneousComponent 1 (v i) * E (frameRelations i) := by
    change homogeneousComponent 3 (∑ i, v i * E (frameRelations i)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact homogeneousComponent_mul_right (linearFrame_quadrics_homogeneous M hM i) 1
  rw [← he, hv, homogeneousComponent_eq_self hf]

end
end PfaffianDescent
