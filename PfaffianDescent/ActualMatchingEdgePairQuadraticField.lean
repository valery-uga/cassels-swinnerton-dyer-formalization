import PfaffianDescent.GaloisPairQuadraticCoefficientField
import PfaffianDescent.ConjugateRescaledRelabelActualGaloisAction
import PfaffianDescent.QuarticGaloisMatching

/-! SOURCE ONLY, UNVERIFIED. The quadratic field for the actual matching
edge-sum pair is derived from the SAME indexed conjugate coordinate basis.
This is not yet a field-of-definition theorem for the entire line ideals. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]

theorem actualMatching_edge_sum_quadratic_field
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (a f : K) (ha : a ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hs)) pi =
        skewTangentDirections a 0 0 0 0 f) :
    let B := (conjugateBasis full p hs).reindex pi.symm
    ∃ E : IntermediateField k K, ∃ _ : FiniteDimensional k E,
      finrank k E = 2 ∧ IsGalois k E ∧
      E = IntermediateField.adjoin k (Set.range (fun m => B 0 m + B 1 m)) ∧
      ∃ xE yE : Fin 4 → E,
        (∀ m, E.val (xE m) = B 0 m + B 1 m) ∧
        (∀ m, E.val (yE m) = B 2 m + B 3 m) := by
  classical
  dsimp only
  let B := (conjugateBasis full p hs).reindex pi.symm
  let x : Fin 4 → K := B 0 + B 1
  let y : Fin 4 → K := B 2 + B 3
  have hact : ∀ g : K ≃ₐ[k] K, ∃ rho : Equiv.Perm (Fin 4),
      (∀ i m, g (B i m) = B (rho i) m) ∧
      (∀ i j, skewTangentDirections a 0 0 0 0 f i j ≠ 0 ↔
        skewTangentDirections a 0 0 0 0 f (rho i) (rho j) ≠ 0) := by
    simpa only [hU] using
      conjugate_rescaled_relabel_actual_galois_action full p v hs l hl pi
  have hpair : ∀ g : K ≃ₐ[k] K,
      ((∀ m, g (x m) = x m) ∧ (∀ m, g (y m) = y m)) ∨
      ((∀ m, g (x m) = y m) ∧ (∀ m, g (y m) = x m)) := by
    intro g
    obtain ⟨rho, hB, hSupport⟩ := hact g
    have hsum (m : Fin 4) : g (x m + y m) = x m + y m := by
      have h : ∑ i : Fin 4, g (B i m) = ∑ i : Fin 4, B i m := by
        simp only [hB]
        exact Equiv.sum_comp rho (fun i => B i m)
      simpa [x, y, Fin.sum_univ_four, map_add, add_assoc] using h
    have hxy : (∀ m, g (x m) = x m) ∨ (∀ m, g (x m) = y m) := by
      rcases matching_edge_cases a f (rho 0) (rho 1)
        ((hSupport 0 1).mp ha) with h | h | h | h
      · exact Or.inl (fun m => by simp [x, map_add, hB, h.1, h.2])
      · exact Or.inl (fun m => by simp [x, map_add, hB, h.1, h.2, add_comm])
      · exact Or.inr (fun m => by simp [x, y, map_add, hB, h.1, h.2])
      · exact Or.inr (fun m => by simp [x, y, map_add, hB, h.1, h.2, add_comm])
    rcases hxy with h | h
    · refine Or.inl ⟨h, ?_⟩
      intro m
      have he := hsum m
      rw [map_add, h] at he
      exact add_left_cancel he
    · refine Or.inr ⟨h, ?_⟩
      intro m
      have he := hsum m
      rw [map_add, h] at he
      linear_combination he
  have hxy : x ≠ y := by
    intro h
    have he := congrArg (fun w : Fin 4 → K => B.repr w 0) h
    simpa [x, y] using he
  have hnotfixed : ¬ ∀ g : K ≃ₐ[k] K, ∀ m, g (x m) = x m := by
    intro hfix
    obtain ⟨g, hg⟩ := indexedEmbeddingAction_transitive full (pi 0) (pi 2)
    let rho := pi.trans ((indexedEmbeddingAction full g).trans pi.symm)
    have hpi (r : Fin 4) : pi (rho r) = indexedEmbeddingAction full g (pi r) := by
      simp only [rho, Equiv.trans_apply, Equiv.apply_symm_apply]
    have hRho0 : rho 0 = 2 := by
      apply pi.injective
      rw [hpi, hg]
    have hB (r m : Fin 4) : g (B r m) = B (rho r) m := by
      simp only [B, Basis.reindex_apply, Equiv.symm_symm, conjugateBasis_apply, hpi]
      exact (indexedEmbeddingAction_apply full g (pi r) (p m)).symm
    have hEdge : skewTangentDirections a 0 0 0 0 f (rho 0) (rho 1) ≠ 0 := by
      have hRaw : conjugateTangentMatrix full p v hs (pi 0) (pi 1) ≠ 0 := by
        have hNonzero : tangentRelabel (rescaleTangentDirections l
            (conjugateTangentMatrix full p v hs)) pi 0 1 ≠ 0 := by
          rw [hU]
          exact ha
        exact (mul_ne_zero_iff.mp hNonzero).2
      have hTarget : conjugateTangentMatrix full p v hs
          (indexedEmbeddingAction full g (pi 0))
          (indexedEmbeddingAction full g (pi 1)) ≠ 0 := by
        rw [← conjugateTangentMatrix_covariance full p v hs g]
        exact fun hz => hRaw (g.injective (hz.trans (map_zero g).symm))
      have hScaled : tangentRelabel (rescaleTangentDirections l
          (conjugateTangentMatrix full p v hs)) pi (rho 0) (rho 1) ≠ 0 := by
        change l (pi (rho 0)) *
          conjugateTangentMatrix full p v hs (pi (rho 0)) (pi (rho 1)) ≠ 0
        exact mul_ne_zero (hl _) (by simpa only [hpi] using hTarget)
      simpa only [hU] using hScaled
    have hRho1 : rho 1 = 3 := by
      rcases matching_edge_cases a f (rho 0) (rho 1) hEdge with h | h | h | h
      · have hz : (2 : Fin 4) = 0 := hRho0.symm.trans h.1
        exact False.elim ((by decide : (2 : Fin 4) ≠ 0) hz)
      · have hz : (2 : Fin 4) = 1 := hRho0.symm.trans h.1
        exact False.elim ((by decide : (2 : Fin 4) ≠ 1) hz)
      · exact h.2
      · have hz : (2 : Fin 4) = 3 := hRho0.symm.trans h.1
        exact False.elim ((by decide : (2 : Fin 4) ≠ 3) hz)
    apply hxy
    funext m
    calc
      x m = g (x m) := (hfix g m).symm
      _ = y m := by simp [x, y, map_add, hB, hRho0, hRho1]
  have hxDef : x = (fun m => B 0 m + B 1 m) := rfl
  have hyDef : y = (fun m => B 2 m + B 3 m) := rfl
  simpa only [hxDef, hyDef, B] using
    PfaffianDescent.galoisPair_quadratic_coefficient_field x y hpair hnotfixed

end PfaffianDescent.QuarticNet
