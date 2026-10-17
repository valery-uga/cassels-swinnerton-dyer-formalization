import PfaffianDescent.QuarticSemilinearNormalization

/-! Full off-diagonal support forces every coordinate of a nonzero weighted
relation to be nonzero. Thus dimension three supplies actual skew rescaling
without arithmetic covariance or an external skew certificate. -/

namespace PfaffianDescent.QuarticNet
open Module
universe u
variable {K : Type u} [Field K]

theorem fullSupport_weightedRelation_coordinates_ne_zero
    (U : Fin 4 → Fin 4 → K) (w : Fin 4 → K) (hw : w ≠ 0)
    (hRelation : w ∈ LinearMap.ker (weightedRelationLinearMap U))
    (hSupport : ∀ r s, r ≠ s → U r s ≠ 0) : ∀ r, w r ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s, w s ≠ 0 := by
    by_contra! h
    exact hw (funext h)
  intro r hr
  have hrs : r ≠ s := by intro h; subst r; exact hs hr
  have h := weightedRelationSpace_offDiagonal U w hRelation r s hrs
  rw [hr, zero_mul] at h
  have hz : w s * U s r = 0 := neg_eq_zero.mp h.symm
  exact (mul_ne_zero hs (hSupport s r hrs.symm)) hz

theorem fullSupport_exists_actual_skew_rescaling
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (hdim : 3 ≤ finrank K (LinearMap.ker (tangentQuadricEvaluationLinearMap U)))
    (hSupport : ∀ r s, r ≠ s → U r s ≠ 0) :
    ∃ l : Fin 4 → K, (∀ r, l r ≠ 0) ∧
      ∀ r s, rescaleTangentDirections l U r s = -rescaleTangentDirections l U s r := by
  obtain ⟨l, hl, hweighted⟩ :=
    exists_nonzero_weighted_relation_of_three_le_finrank_ker U hdim
  have hRel : l ∈ LinearMap.ker (weightedRelationLinearMap U) :=
    (mem_ker_weightedRelationLinearMap_iff U l).mpr
      (tangentQuadric_relations_of_weighted_eq_zero U l hweighted)
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ :=
    (mem_ker_weightedRelationLinearMap_iff U l).mp hRel
  exact ⟨l, fullSupport_weightedRelation_coordinates_ne_zero U l hl hRel hSupport,
    rescaleTangentDirections_skew_of_relations U l hdiag h01 h02 h03 h12 h13 h23⟩

end PfaffianDescent.QuarticNet
