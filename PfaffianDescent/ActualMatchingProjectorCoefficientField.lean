import PfaffianDescent.BasisMatchingProjectorInvariance
import PfaffianDescent.ActualMatchingEdgePairQuadraticField

/-! SOURCE ONLY, UNVERIFIED. The SAME actual quadratic edge field contains
EVERY coefficient of the actual line projector. The action is constructed
from the original embeddings and basis; no Galois-action or descent input. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]

theorem actualMatching_projector_mem_edge_field
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p : Fin 4 → L)
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (pi : Equiv.Perm (Fin 4)) (m n : Fin 4) :
    let B := (conjugateBasis full p hs).reindex pi.symm
    matchingEdgeProjectorMatrix B m n ∈
      IntermediateField.adjoin k (Set.range (fun j => B 0 j + B 1 j)) := by
  dsimp only
  let B := (conjugateBasis full p hs).reindex pi.symm
  apply (PfaffianDescent.mem_generatedCoordinateField_iff_fixed_by_coordinate_stabilizer
    (fun j => B 0 j + B 1 j) _).mpr
  intro g hx
  let rho := pi.trans ((indexedEmbeddingAction full g).trans pi.symm)
  have hpi (r : Fin 4) : pi (rho r) = indexedEmbeddingAction full g (pi r) := by
    simp only [rho, Equiv.trans_apply, Equiv.apply_symm_apply]
  have hB (r j : Fin 4) : g (B r j) = B (rho r) j := by
    simp only [B, Basis.reindex_apply, Equiv.symm_symm, conjugateBasis_apply, hpi]
    exact (indexedEmbeddingAction_apply full g (pi r) (p j)).symm
  exact matchingEdgeProjectorMatrix_fixed B g rho hB hx m n

theorem actualMatching_projector_quadratic_field
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
      ∃ P : Matrix (Fin 4) (Fin 4) E,
        P.map E.val.toRingHom = matchingEdgeProjectorMatrix B := by
  classical
  dsimp only
  let B := (conjugateBasis full p hs).reindex pi.symm
  obtain ⟨E, hFD, hdeg, hGal, hE, xE, yE, hxE, hyE⟩ :=
    actualMatching_edge_sum_quadratic_field full p v hs l hl pi a f ha hU
  refine ⟨E, hFD, hdeg, hGal, hE, ?_⟩
  let P : Matrix (Fin 4) (Fin 4) E := fun m n =>
    ⟨matchingEdgeProjectorMatrix B m n, by
      rw [hE]
      exact actualMatching_projector_mem_edge_field full p hs pi m n⟩
  refine ⟨P, ?_⟩
  rfl

end PfaffianDescent.QuarticNet
