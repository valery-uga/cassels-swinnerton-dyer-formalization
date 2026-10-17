import PfaffianDescent.QuarticTangentGraph
import PfaffianDescent.QuarticConjugateCoordinates

/-!
# Support classification after skew normalization

Rescaling tangent-direction representatives by nonzero factors does not
change their support.  Thus a normalized skew tangent matrix inherits the
regular support graph forced by Galois covariance of the original matrix.
-/

namespace PfaffianDescent
namespace QuarticNet

variable {K : Type*} [Field K]

private theorem nonzeroEdge_rescale (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0)
    (U : Fin 4 → Fin 4 → K) (i j : Fin 4) :
    nonzeroEdge (rescaleTangentDirections l U i j) = nonzeroEdge (U i j) := by
  apply nonzeroEdge_congr
  simp [rescaleTangentDirections, hl i]

theorem rescale_supportDegree (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0)
    (U : Fin 4 → Fin 4 → K) (i : Fin 4) :
    supportDegree (rescaleTangentDirections l U) i = supportDegree U i := by
  unfold supportDegree
  apply Finset.sum_congr rfl
  intro j _
  rw [nonzeroEdge_rescale l hl U i j]

theorem rescaled_tangent_support_classification [Infinite K]
    (U : Fin 4 → Fin 4 → K) (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0)
    (hdiag : ∀ i, U i i = 0)
    (hskew : ∀ i j, rescaleTangentDirections l U i j =
      -rescaleTangentDirections l U j i)
    (hcov : ∀ i j : Fin 4,
      ∃ (p : Equiv.Perm (Fin 4)) (sigma : K ≃+* K) (r s : Fin 4 → K),
        p i = j ∧ (∀ m, r m ≠ 0) ∧ (∀ m, s m ≠ 0) ∧
        ∀ m n, sigma (U m n) = r m * s n * U (p m) (p n))
    (hrow : ∀ i, ∃ j, U i j ≠ 0)
    (hmissing : ∃ i j, i ≠ j ∧ U i j = 0) :
    matchingPattern (nonzeroEdge (U 0 1)) (nonzeroEdge (U 0 2))
      (nonzeroEdge (U 0 3)) (nonzeroEdge (U 1 2)) (nonzeroEdge (U 1 3))
      (nonzeroEdge (U 2 3)) ∨
    matchingPattern (!(nonzeroEdge (U 0 1))) (!(nonzeroEdge (U 0 2)))
      (!(nonzeroEdge (U 0 3))) (!(nonzeroEdge (U 1 2))) (!(nonzeroEdge (U 1 3)))
      (!(nonzeroEdge (U 2 3))) := by
  have hregular : ∀ i j, supportDegree (rescaleTangentDirections l U) i =
      supportDegree (rescaleTangentDirections l U) j := by
    intro i j
    rw [rescale_supportDegree l hl U i, rescale_supportDegree l hl U j]
    exact transitive_covariance_regular U hcov i j
  have hrow' : ∀ i, ∃ j, rescaleTangentDirections l U i j ≠ 0 := by
    intro i
    obtain ⟨j, hj⟩ := hrow i
    exact ⟨j, mul_ne_zero (hl i) hj⟩
  have hmissing' : ∃ i j, i ≠ j ∧ rescaleTangentDirections l U i j = 0 := by
    obtain ⟨i, j, hij, hU⟩ := hmissing
    exact ⟨i, j, hij, by simp [rescaleTangentDirections, hU]⟩
  have hclass := tangent_support_classification (rescaleTangentDirections l U)
    (fun i => by simp [rescaleTangentDirections, hdiag i]) hskew hregular hrow' hmissing'
  simpa only [nonzeroEdge_rescale l hl U 0 1, nonzeroEdge_rescale l hl U 0 2,
    nonzeroEdge_rescale l hl U 0 3, nonzeroEdge_rescale l hl U 1 2,
    nonzeroEdge_rescale l hl U 1 3, nonzeroEdge_rescale l hl U 2 3] using hclass

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [Algebra k K]

theorem conjugate_tangent_support_classification [Normal k K] [Infinite K]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (hp : p 0 = 1) (hv0 : v 0 = 0) (hv : v ≠ 0)
    (hmissing : ∃ i j, i ≠ j ∧ conjugateTangentMatrix e p v hspan i j = 0) :
    matchingPattern (nonzeroEdge (conjugateTangentMatrix e p v hspan 0 1))
      (nonzeroEdge (conjugateTangentMatrix e p v hspan 0 2))
      (nonzeroEdge (conjugateTangentMatrix e p v hspan 0 3))
      (nonzeroEdge (conjugateTangentMatrix e p v hspan 1 2))
      (nonzeroEdge (conjugateTangentMatrix e p v hspan 1 3))
      (nonzeroEdge (conjugateTangentMatrix e p v hspan 2 3)) ∨
    matchingPattern (!(nonzeroEdge (conjugateTangentMatrix e p v hspan 0 1)))
      (!(nonzeroEdge (conjugateTangentMatrix e p v hspan 0 2)))
      (!(nonzeroEdge (conjugateTangentMatrix e p v hspan 0 3)))
      (!(nonzeroEdge (conjugateTangentMatrix e p v hspan 1 2)))
      (!(nonzeroEdge (conjugateTangentMatrix e p v hspan 1 3)))
      (!(nonzeroEdge (conjugateTangentMatrix e p v hspan 2 3))) := by
  apply rescaled_tangent_support_classification
  · exact hl
  · exact conjugateTangentMatrix_diagonal e p v hspan
  · simpa only [rescaleTangentDirections] using hskew
  · exact conjugateTangentMatrix_transitive_covariance e p v hspan
  · exact conjugateTangentMatrix_row_nonzero e p v hspan hp hv0 hv
  · exact hmissing

/-- After skew normalization, the conjugate tangent matrix has either full
off-diagonal support, matching support, or four-cycle support. -/
theorem conjugate_tangent_full_support_or_support_classification [Normal k K] [Infinite K]
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun σ : L →ₐ[k] K => fun i => σ (p i))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (hp : p 0 = 1) (hv0 : v 0 = 0) (hv : v ≠ 0) :
    (∀ i j, i ≠ j → conjugateTangentMatrix e p v hspan i j ≠ 0) ∨
    matchingPattern (nonzeroEdge (conjugateTangentMatrix e p v hspan 0 1))
      (nonzeroEdge (conjugateTangentMatrix e p v hspan 0 2))
      (nonzeroEdge (conjugateTangentMatrix e p v hspan 0 3))
      (nonzeroEdge (conjugateTangentMatrix e p v hspan 1 2))
      (nonzeroEdge (conjugateTangentMatrix e p v hspan 1 3))
      (nonzeroEdge (conjugateTangentMatrix e p v hspan 2 3)) ∨
    matchingPattern (!(nonzeroEdge (conjugateTangentMatrix e p v hspan 0 1)))
      (!(nonzeroEdge (conjugateTangentMatrix e p v hspan 0 2)))
      (!(nonzeroEdge (conjugateTangentMatrix e p v hspan 0 3)))
      (!(nonzeroEdge (conjugateTangentMatrix e p v hspan 1 2)))
      (!(nonzeroEdge (conjugateTangentMatrix e p v hspan 1 3)))
      (!(nonzeroEdge (conjugateTangentMatrix e p v hspan 2 3))) := by
  by_cases hfull : ∀ i j, i ≠ j → conjugateTangentMatrix e p v hspan i j ≠ 0
  · exact Or.inl hfull
  · right
    apply conjugate_tangent_support_classification e p v hspan l hl hskew hp hv0 hv
    push Not at hfull
    exact hfull

end QuarticNet
end PfaffianDescent
