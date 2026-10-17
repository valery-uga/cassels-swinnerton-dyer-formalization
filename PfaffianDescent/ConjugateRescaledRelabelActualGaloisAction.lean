import PfaffianDescent.QuarticConjugateCoordinates
import PfaffianDescent.QuarticTangentRelabeling

/-! SOURCE ONLY, UNVERIFIED. Derive the actual Galois permutation and support
invariance from the SAME indexed residue-field embeddings. Independently
chosen nonzero tangent row weights need not be Galois fixed. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K]

theorem conjugate_rescaled_relabel_actual_galois_action
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0) (pi : Equiv.Perm (Fin 4)) :
    let B := (conjugateBasis full p hspan).reindex pi.symm
    let U := tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hspan)) pi
    ∀ g : K ≃ₐ[k] K, ∃ rho : Equiv.Perm (Fin 4),
      (∀ i m, g (B i m) = B (rho i) m) ∧
      (∀ i j, U i j ≠ 0 ↔ U (rho i) (rho j) ≠ 0) := by
  dsimp only
  intro g
  let rho := pi.trans ((indexedEmbeddingAction full g).trans pi.symm)
  have hpi (i : Fin 4) : pi (rho i) = indexedEmbeddingAction full g (pi i) := by
    simp only [rho, Equiv.trans_apply, Equiv.apply_symm_apply]
  refine ⟨rho, ?_, ?_⟩
  · intro i m
    simp only [Basis.reindex_apply, Equiv.symm_symm, conjugateBasis_apply, hpi]
    exact (indexedEmbeddingAction_apply full g (pi i) (p m)).symm
  · intro i j
    have hraw : conjugateTangentMatrix full p v hspan (pi i) (pi j) ≠ 0 ↔
        conjugateTangentMatrix full p v hspan
          (indexedEmbeddingAction full g (pi i))
          (indexedEmbeddingAction full g (pi j)) ≠ 0 := by
      rw [← conjugateTangentMatrix_covariance full p v hspan g (pi i) (pi j)]
      simp
    change l (pi i) * conjugateTangentMatrix full p v hspan (pi i) (pi j) ≠ 0 ↔
      l (pi (rho i)) * conjugateTangentMatrix full p v hspan
        (pi (rho i)) (pi (rho j)) ≠ 0
    rw [hpi i, hpi j]
    constructor
    · intro h
      exact mul_ne_zero (hl _) (hraw.mp (mul_ne_zero_iff.mp h).2)
    · intro h
      exact mul_ne_zero (hl _) (hraw.mpr (mul_ne_zero_iff.mp h).2)

end PfaffianDescent.QuarticNet
