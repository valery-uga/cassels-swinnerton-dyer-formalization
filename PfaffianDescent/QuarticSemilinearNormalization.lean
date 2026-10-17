import PfaffianDescent.QuarticNetLinearAlgebra

/-!
# Semilinear normalization of the tangent matrix

Transitive semilinear covariance transports weighted tangent relations among
the four rows.  A nonzero relation can therefore be moved to every coordinate,
and over an infinite field one relation has full support.  Row-rescaling by
that relation makes the tangent matrix skew-symmetric.
-/

namespace PfaffianDescent
namespace QuarticNet

variable {K : Type*} [Field K] [Infinite K]

noncomputable def monomialTransform (p : Equiv.Perm (Fin 4)) (sigma : K ≃+* K)
    (w x : Fin 4 → K) : Fin 4 → K :=
  fun j => w j * sigma (x (p.symm j))

theorem monomialTransform_nonzero (p : Equiv.Perm (Fin 4)) (sigma : K ≃+* K)
    (w x : Fin 4 → K) (i : Fin 4) (hw : w (p i) ≠ 0) (hx : x i ≠ 0) :
    monomialTransform p sigma w x (p i) ≠ 0 := by
  simp only [monomialTransform, Equiv.symm_apply_apply]
  exact mul_ne_zero hw ((map_ne_zero sigma).mpr hx)

theorem mem_weightedRelationSpace_iff (U : Fin 4 → Fin 4 → K) (l : Fin 4 → K) :
    l ∈ LinearMap.ker (weightedRelationLinearMap U) ↔
      ∀ i j : Fin 4, i < j → l i * U i j = -(l j * U j i) := by
  constructor
  · intro hl i j hij
    obtain ⟨h01, h02, h03, h12, h13, h23⟩ :=
      (mem_ker_weightedRelationLinearMap_iff U l).mp hl
    fin_cases i <;> fin_cases j <;> simp_all [← add_eq_zero_iff_eq_neg]
  · intro hl
    apply (mem_ker_weightedRelationLinearMap_iff U l).mpr
    exact ⟨eq_neg_iff_add_eq_zero.mp (hl 0 1 (by decide)),
      eq_neg_iff_add_eq_zero.mp (hl 0 2 (by decide)),
      eq_neg_iff_add_eq_zero.mp (hl 0 3 (by decide)),
      eq_neg_iff_add_eq_zero.mp (hl 1 2 (by decide)),
      eq_neg_iff_add_eq_zero.mp (hl 1 3 (by decide)),
      eq_neg_iff_add_eq_zero.mp (hl 2 3 (by decide))⟩

theorem weightedRelationSpace_offDiagonal (U : Fin 4 → Fin 4 → K)
    (l : Fin 4 → K) (hl : l ∈ LinearMap.ker (weightedRelationLinearMap U))
    (i j : Fin 4) (hij : i ≠ j) :
    l i * U i j = -(l j * U j i) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact (mem_weightedRelationSpace_iff U l).mp hl i j h
  · have h' := (mem_weightedRelationSpace_iff U l).mp hl j i h
    simpa using congrArg (fun z : K => -z) h'.symm

theorem covariance_preserves_weightedRelations (U : Fin 4 → Fin 4 → K)
    (p : Equiv.Perm (Fin 4)) (sigma : K ≃+* K) (r s : Fin 4 → K)
    (hs : ∀ i, s i ≠ 0)
    (hcov : ∀ i j, sigma (U i j) = r i * s j * U (p i) (p j))
    (l : Fin 4 → K) (hl : l ∈ LinearMap.ker (weightedRelationLinearMap U)) :
    monomialTransform p sigma (fun j => r (p.symm j) / s (p.symm j)) l ∈
      LinearMap.ker (weightedRelationLinearMap U) := by
  apply (mem_weightedRelationSpace_iff U _).mpr
  intro i j hij
  have hne : p.symm i ≠ p.symm j := fun h => (ne_of_lt hij) (p.symm.injective h)
  have h := congrArg sigma
    (weightedRelationSpace_offDiagonal U l hl (p.symm i) (p.symm j) hne)
  simp only [map_mul, map_neg, hcov, Equiv.apply_symm_apply] at h
  dsimp [monomialTransform]
  field_simp [hs]
  linear_combination h

theorem exists_full_weightedRelation_of_covariance (U : Fin 4 → Fin 4 → K)
    (hdim : 3 ≤ Module.finrank K (LinearMap.ker (tangentQuadricEvaluationLinearMap U)))
    (hcov : ∀ i j : Fin 4,
      ∃ (p : Equiv.Perm (Fin 4)) (sigma : K ≃+* K) (r s : Fin 4 → K),
        p i = j ∧ (∀ m, r m ≠ 0) ∧ (∀ m, s m ≠ 0) ∧
        ∀ m n, sigma (U m n) = r m * s n * U (p m) (p n)) :
    ∃ l : Fin 4 → K, l ∈ LinearMap.ker (weightedRelationLinearMap U) ∧
      ∀ i, l i ≠ 0 := by
  obtain ⟨l, hl, hweighted⟩ :=
    exists_nonzero_weighted_relation_of_three_le_finrank_ker U hdim
  have hlR : l ∈ LinearMap.ker (weightedRelationLinearMap U) :=
    (mem_ker_weightedRelationLinearMap_iff U l).mpr
      (tangentQuadric_relations_of_weighted_eq_zero U l hweighted)
  obtain ⟨i, hi⟩ : ∃ i, l i ≠ 0 := by
    by_contra! h
    exact hl (funext h)
  obtain ⟨w, hw, hwne⟩ := exists_weighted_relation_all_coordinates_ne_zero U (by
    intro j
    obtain ⟨p, sigma, r, s, hp, hr, hs, hU⟩ := hcov i j
    let t : Fin 4 → K := fun m => r (p.symm m) / s (p.symm m)
    refine ⟨monomialTransform p sigma t l,
      covariance_preserves_weightedRelations U p sigma r s hs hU l hlR, ?_⟩
    rw [← hp]
    exact monomialTransform_nonzero p sigma t l i (by
      dsimp [t]
      simpa using div_ne_zero (hr i) (hs i)) hi)
  exact ⟨w, hw, hwne⟩

theorem skew_normalization_of_transitive_covariance (U : Fin 4 → Fin 4 → K)
    (hdiag : ∀ i, U i i = 0)
    (hdim : 3 ≤ Module.finrank K (LinearMap.ker (tangentQuadricEvaluationLinearMap U)))
    (hcov : ∀ i j : Fin 4,
      ∃ (p : Equiv.Perm (Fin 4)) (sigma : K ≃+* K) (r s : Fin 4 → K),
        p i = j ∧ (∀ m, r m ≠ 0) ∧ (∀ m, s m ≠ 0) ∧
        ∀ m n, sigma (U m n) = r m * s n * U (p m) (p n)) :
    ∃ l : Fin 4 → K, (∀ i, l i ≠ 0) ∧ ∀ i j,
      l i * U i j = -(l j * U j i) := by
  obtain ⟨l, hl, hne⟩ := exists_full_weightedRelation_of_covariance U hdim hcov
  obtain ⟨h01, h02, h03, h12, h13, h23⟩ :=
    (mem_ker_weightedRelationLinearMap_iff U l).mp hl
  refine ⟨l, hne, ?_⟩
  simpa only [rescaleTangentDirections] using
    rescaleTangentDirections_skew_of_relations U l hdiag h01 h02 h03 h12 h13 h23

end QuarticNet
end PfaffianDescent
