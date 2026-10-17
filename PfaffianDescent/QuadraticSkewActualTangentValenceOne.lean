import PfaffianDescent.QuarticZeroEntrySupportGraph

/-! SOURCE ONLY. Native graph valence one recovers the literal unique
neighbor predicate; conjugate covariance derives regularity internally. -/
noncomputable section
namespace PfaffianDescent.QuarticNet
universe u

variable {K : Type u} [Field K]

theorem tangentSupport_degree_one_unique_neighbor
    (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ r, U r r = 0)
    (hskew : ∀ r s, U r s = -U s r)
    (hdegree : ∀ r, supportDegree U r = 1) :
    ∀ r, ∃! s, U r s ≠ 0 := by
  classical
  intro r
  have hg : (tangentSupportGraph U hdiag hskew).degree r = 1 :=
    (tangentSupportGraph_degree U hdiag hskew r).trans (hdegree r)
  exact SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hg

theorem tangentSupport_unique_neighbor_missing_entry
    (U : Fin 4 → Fin 4 → K)
    (hOne : ∀ r, ∃! s, U r s ≠ 0) :
    ∃ r s, r ≠ s ∧ U r s = 0 := by
  classical
  by_cases h01 : U 0 1 = 0
  · exact ⟨0, 1, by decide, h01⟩
  · have h02 : U 0 2 = 0 := by
      by_contra h02
      obtain ⟨s, hs, hUnique⟩ := hOne 0
      have he : (1 : Fin 4) = 2 :=
        (hUnique 1 h01).trans (hUnique 2 h02).symm
      exact (by decide : (1 : Fin 4) ≠ 2) he
    exact ⟨0, 2, by decide, h02⟩

variable {k L : Type u} [Field k] [Field L]
  [Algebra k L] [Algebra k K] [Normal k K]

theorem actual_conjugate_rescaled_supportDegree_regular
    (full : Fin 4 ≃ (L →ₐ[k] K)) (b v : Fin 4 → L)
    (hs : Submodule.span K (Set.range (fun sigma : L →ₐ[k] K =>
      fun r => sigma (b r))) = ⊤)
    (l : Fin 4 → K) (hl : ∀ r, l r ≠ 0) :
    ∀ r s, supportDegree (rescaleTangentDirections l
      (conjugateTangentMatrix full b v hs)) r =
      supportDegree (rescaleTangentDirections l
        (conjugateTangentMatrix full b v hs)) s := by
  intro r s
  rw [rescale_supportDegree l hl, rescale_supportDegree l hl]
  exact transitive_covariance_regular _
    (conjugateTangentMatrix_transitive_covariance full b v hs) r s

end PfaffianDescent.QuarticNet
