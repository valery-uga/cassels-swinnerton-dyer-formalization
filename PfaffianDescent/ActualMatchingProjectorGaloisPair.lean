import PfaffianDescent.BasisMatchingProjectorActualLineIdeal
import PfaffianDescent.ConjugateRescaledRelabelActualGaloisAction
import PfaffianDescent.QuarticGaloisMatching

/-! SOURCE ONLY, UNVERIFIED. Actual Galois action fixes the matching
projector or interchanges it with its complementary projector. No Galois
pair/covariance premise in the actual factory. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
open Module
open scoped BigOperators
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsGalois k K]

theorem matchingEdgeProjectorMatrix_complement_entry
    (B : Basis (Fin 4) K (Fin 4 → K)) (m n : Fin 4) :
    (1 - matchingEdgeProjectorMatrix B) m n =
      B 2 m * B.repr (Pi.single n 1) 2 +
        B 3 m * B.repr (Pi.single n 1) 3 := by
  classical
  rw [matchingEdgeComplementMatrix_factor B,
    ← basisReprCoordinateMatrix_eq_inverse B]
  simp [Matrix.mul_apply, Matrix.diagonal, basisCoordinateMatrix,
    basisReprCoordinateMatrix, Fin.sum_univ_four]

theorem actualMatching_projector_galois_pair
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (a f : K) (ha : a ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hs)) pi =
        skewTangentDirections a 0 0 0 0 f) :
    let B := (conjugateBasis full p hs).reindex pi.symm
    ∀ g : K ≃ₐ[k] K,
      (matchingEdgeProjectorMatrix B).map g.toRingHom = matchingEdgeProjectorMatrix B ∨
      (matchingEdgeProjectorMatrix B).map g.toRingHom = 1 - matchingEdgeProjectorMatrix B := by
  classical
  dsimp only
  let B := (conjugateBasis full p hs).reindex pi.symm
  intro g
  obtain ⟨rho, hB, hSupport⟩ :=
    conjugate_rescaled_relabel_actual_galois_action full p v hs l hl pi g
  have hSup : ∀ i j, skewTangentDirections a 0 0 0 0 f i j ≠ 0 ↔
      skewTangentDirections a 0 0 0 0 f (rho i) (rho j) ≠ 0 := by
    simpa only [hU] using hSupport
  have hr (n i : Fin 4) : g (B.repr (Pi.single n 1) i) =
      B.repr (Pi.single n 1) (rho i) := by
    have hstd : (fun j : Fin 4 => g ((Pi.single n (1 : K) : Fin 4 → K) j)) = Pi.single n 1 := by
      funext j
      by_cases h : n = j <;> simp [Pi.single_apply, h]
    simpa only [hstd] using
      (permutedBasis_repr_covariance B g rho hB (Pi.single n 1) i).symm
  have hentry (m n : Fin 4) :
      ((matchingEdgeProjectorMatrix B).map g.toRingHom) m n =
        B (rho 0) m * B.repr (Pi.single n 1) (rho 0) +
          B (rho 1) m * B.repr (Pi.single n 1) (rho 1) := by
    change g (B 0 m * B.repr (Pi.single n 1) 0 +
      B 1 m * B.repr (Pi.single n 1) 1) = _
    rw [map_add, map_mul, map_mul, hB, hB, hr, hr]
  rcases matching_edge_cases a f (rho 0) (rho 1) ((hSup 0 1).mp ha) with
    h | h | h | h
  · apply Or.inl
    ext m n
    rw [hentry]
    simp only [matchingEdgeProjectorMatrix, h.1, h.2, B]
  · apply Or.inl
    ext m n
    rw [hentry]
    simp only [matchingEdgeProjectorMatrix, h.1, h.2, B]
    exact add_comm _ _
  · apply Or.inr
    ext m n
    rw [hentry, matchingEdgeProjectorMatrix_complement_entry]
    simp only [h.1, h.2, B]
  · apply Or.inr
    ext m n
    rw [hentry, matchingEdgeProjectorMatrix_complement_entry]
    simp only [h.1, h.2, B]
    exact add_comm _ _

end PfaffianDescent.QuarticNet
