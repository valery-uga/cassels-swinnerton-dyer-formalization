import PfaffianDescent.QuarticZeroEntrySupportGraph

/-! Source-only, UNVERIFIED.  The actual conjugate tangent matrix supplies
transitivity, semilinear covariance and nonzero rows internally.  Its
normalized zero-entry support is therefore a matching or a four-cycle. -/

noncomputable section
namespace PfaffianDescent.QuarticNet
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [Normal k K]

theorem conjugateQuartic_zero_entry_support_graph
    (e : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun i => sigma (p i))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ i, l i ≠ 0)
    (hskew : ∀ i j, l i * conjugateTangentMatrix e p v hspan i j =
      -(l j * conjugateTangentMatrix e p v hspan j i))
    (hp : p 0 = 1) (hv0 : v 0 = 0) (hv : v ≠ 0)
    (hmissing : ∃ i j, i ≠ j ∧
      rescaleTangentDirections l (conjugateTangentMatrix e p v hspan) i j = 0) :
    ZeroEntryTangentSupportClassification
      (rescaleTangentDirections l (conjugateTangentMatrix e p v hspan)) := by
  apply zero_entry_rescaled_transitive_skew_support_graph
    (conjugateTangentMatrix e p v hspan) l hl
    (conjugateTangentMatrix_diagonal e p v hspan)
  · exact hskew
  · exact conjugateTangentMatrix_transitive_covariance e p v hspan
  · exact conjugateTangentMatrix_row_nonzero e p v hspan hp hv0 hv
  · exact hmissing

end PfaffianDescent.QuarticNet
