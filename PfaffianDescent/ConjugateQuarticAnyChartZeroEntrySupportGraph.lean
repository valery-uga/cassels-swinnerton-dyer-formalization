import PfaffianDescent.ConjugateTangentAnyChartRowNonzero
import PfaffianDescent.QuarticZeroEntrySupportGraph

/-! SOURCE ONLY, UNVERIFIED. Derive matching/C4 support and common valence
from the SAME original-j tangent matrix. No support-graph certificate or
six-entry support assumption occurs. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
universe u
variable {k L K : Type u} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [Normal k K]

theorem conjugateQuartic_any_chart_zero_entry_support_graph
    (full : Fin 4 ≃ (L →ₐ[k] K)) (p v : Fin 4 → L)
    (hspan : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun m => sigma (p m))) = ⊤)
    (j : Fin 4) (hp : p j = 1) (hvj : v j = 0) (hv : v ≠ 0)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0)
    (hskew : ∀ r s, rescaleTangentDirections l (conjugateTangentMatrix full p v hspan) r s =
      -rescaleTangentDirections l (conjugateTangentMatrix full p v hspan) s r)
    (hmissing : ∃ r s, r ≠ s ∧
      rescaleTangentDirections l (conjugateTangentMatrix full p v hspan) r s = 0) :
    ZeroEntryTangentSupportClassification
      (rescaleTangentDirections l (conjugateTangentMatrix full p v hspan)) := by
  apply zero_entry_rescaled_transitive_skew_support_graph
    (conjugateTangentMatrix full p v hspan) l hl
    (conjugateTangentMatrix_diagonal full p v hspan)
  · exact hskew
  · exact conjugateTangentMatrix_transitive_covariance full p v hspan
  · exact conjugateTangentMatrix_row_nonzero_at_normalized_chart full p v hspan j hp hvj hv
  · exact hmissing

end PfaffianDescent.QuarticNet
