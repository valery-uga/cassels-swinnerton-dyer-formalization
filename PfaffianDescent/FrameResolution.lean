import PfaffianDescent.FrameGradedExactness

namespace PfaffianDescent
open MvPolynomial Module
open scoped BigOperators
section
variable {K : Type*} [Field K]

lemma homogeneousComponent_sum_of_bound {σ : Type*} (p : MvPolynomial σ K) (N : ℕ)
    (hN : p.totalDegree + 1 ≤ N) :
    (∑ d ∈ Finset.range N, homogeneousComponent d p) = p := by
  calc
    _ = ∑ d ∈ Finset.range (p.totalDegree+1), homogeneousComponent d p := by
      symm
      apply Finset.sum_subset (Finset.range_mono hN)
      intro d hd hn
      apply homogeneousComponent_eq_zero
      simp only [Finset.mem_range] at hd hn
      omega
    _ = p := sum_homogeneousComponent p

lemma frameLastMap_homogeneous_kernel_mem (d : ℕ) (v : Fin 5 → FrameHomogeneous K d)
    (hv : frameGradedLast d v = 0) :
    frameVectorInclusion d v ∈ LinearMap.range (frameMiddleMap (K := K)) := by
  cases d with
  | zero =>
      have hmem : v ∈ LinearMap.ker (frameGradedLast 0) := hv
      rw [frameGradedLast_ker_zero, Submodule.mem_bot] at hmem
      rw [hmem, map_zero]
      exact Submodule.zero_mem _
  | succ d =>
      have hmem : v ∈ LinearMap.ker (frameGradedLast (d+1)) := hv
      rw [← frameGradedMiddle_exact] at hmem
      obtain ⟨w, hw⟩ := hmem
      refine ⟨frameVectorInclusion d w, ?_⟩
      rw [← frameGradedMiddle_val, hw]

lemma frameLastMap_component_mem (d : ℕ) (v : Fin 5 → MvPolynomial (Fin 4) K)
    (hv : frameLastMap v = 0) :
    (fun i => homogeneousComponent d (v i)) ∈ LinearMap.range (frameMiddleMap (K := K)) := by
  let w : Fin 5 → FrameHomogeneous K d := fun i =>
    ⟨homogeneousComponent d (v i), homogeneousComponent_mem d (v i)⟩
  have hw : frameGradedLast d w = 0 := by
    apply Subtype.ext
    rw [frameGradedLast_val, Submodule.coe_zero]
    change frameLastMap (fun i => homogeneousComponent d (v i)) = 0
    rw [frameLastMap_component, hv, map_zero]
  exact frameLastMap_homogeneous_kernel_mem d w hw

/-- Exactness at the remaining free module: every polynomial syzygy among the
five frame quadrics is an image of the explicit alternating linear matrix. -/
theorem frameMiddleMap_range_eq_last_ker :
    LinearMap.range (frameMiddleMap (K := K)) = LinearMap.ker frameLastMap := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr frameLastMap_comp_middle
  · intro v hv
    classical
    let N := Finset.univ.sup (fun i : Fin 5 => (v i).totalDegree + 1)
    have hsum : (∑ d ∈ Finset.range N, fun i => homogeneousComponent d (v i)) = v := by
      funext i
      rw [Finset.sum_apply]
      apply homogeneousComponent_sum_of_bound
      exact Finset.le_sup (f := fun j : Fin 5 => (v j).totalDegree + 1) (Finset.mem_univ i)
    rw [← hsum]
    exact Submodule.sum_mem _ (fun d _ => frameLastMap_component_mem d v hv)

/-- The explicit projective-frame free resolution, including all three nontrivial
exactness assertions and the surjective quotient augmentation. -/
theorem frame_free_resolution :
    Function.Injective (frameFirstMap (K := K)) ∧
    LinearMap.range (frameFirstMap (K := K)) = LinearMap.ker frameMiddleMap ∧
    LinearMap.range (frameMiddleMap (K := K)) = LinearMap.ker frameLastMap ∧
    LinearMap.range (frameLastMap (K := K)) = frameIdeal ∧
    Function.Surjective (Ideal.Quotient.mkₐ K (frameIdeal (K := K))) ∧
    ∀ p : MvPolynomial (Fin 4) K,
      Ideal.Quotient.mkₐ K frameIdeal p = 0 ↔ p ∈ LinearMap.range frameLastMap :=
  ⟨frameFirstMap_injective, frameFirstMap_range_eq_middle_ker,
    frameMiddleMap_range_eq_last_ker, frameLastMap_range, frame_augmentation_exact⟩

end
end PfaffianDescent
