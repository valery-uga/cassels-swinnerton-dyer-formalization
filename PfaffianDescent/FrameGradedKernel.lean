import PfaffianDescent.FrameHomogeneousMaps

namespace PfaffianDescent
open MvPolynomial Module
open scoped BigOperators
section
variable {K : Type*} [Field K]

lemma frameRelation_zero_ne : frameRelations (K := K) 0 ≠ 0 := by
  change (X 0 : MvPolynomial (Fin 4) K) * X 2 - X 0 * X 1 ≠ 0
  rw [← mul_sub]
  exact mul_ne_zero (X_ne_zero 0) frame_difference_prime.ne_zero

lemma frameGradedMiddle_kernel_lift (d : ℕ) (v : Fin 5 → FrameHomogeneous K d)
    (hv : frameGradedMiddle d v = 0) :
    ∃ r : MvPolynomial (Fin 4) K, frameVectorInclusion d v = r • frameRelations := by
  have h := congrArg (frameVectorInclusion (d+1)) hv
  rw [frameGradedMiddle_val, map_zero] at h
  exact frameMatrix_kernel _ h

/-- Exactness at the first rank-five module also holds degree by degree. -/
theorem frameGradedFirst_range_eq_middle_ker (d : ℕ) :
    LinearMap.range (frameGradedFirst (K := K) d) =
      LinearMap.ker (frameGradedMiddle (d+2)) := by
  ext v
  constructor
  · rintro ⟨r, rfl⟩
    rw [LinearMap.mem_ker]
    apply frameVectorInclusion_injective (d+2+1)
    rw [frameGradedMiddle_val, frameGradedFirst_val, map_zero]
    exact LinearMap.mem_ker.mp ((frameFirstMap_range_eq_middle_ker (K := K)) ▸
      (show frameFirstMap r.val ∈ LinearMap.range frameFirstMap from ⟨r.val, rfl⟩))
  · intro hv
    obtain ⟨r, hr⟩ := frameGradedMiddle_kernel_lift (d+2) v hv
    have hr0 : r * frameRelations 0 = (v 0).val := (congrFun hr 0).symm
    have hh : (r * frameRelations 0).IsHomogeneous (d+2) := hr0 ▸ (v 0).property
    have hd : r.IsHomogeneous d := homogeneous_of_mul_right
      (frameRelations_homogeneous 0) frameRelation_zero_ne hh
    refine ⟨⟨r, hd⟩, ?_⟩
    apply frameVectorInclusion_injective (d+2)
    exact hr.symm

lemma frameGradedMiddle_injective_low (d : ℕ) (hd : d < 2) :
    Function.Injective (frameGradedMiddle (K := K) d) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  obtain ⟨r, hr⟩ := frameGradedMiddle_kernel_lift d v hv
  have hr0 : r * frameRelations 0 = (v 0).val := (congrFun hr 0).symm
  have hh : (r * frameRelations 0).IsHomogeneous d := hr0 ▸ (v 0).property
  have hz : r = 0 := eq_zero_of_mul_homogeneous_lt
    (frameRelations_homogeneous 0) frameRelation_zero_ne hh hd
  apply frameVectorInclusion_injective d
  rw [hr, hz, zero_smul, map_zero]

lemma frameGradedMiddle_ker_finrank (d : ℕ) :
    finrank K (LinearMap.ker (frameGradedMiddle (K := K) (d+2))) = (d+3).choose 3 := by
  rw [← frameGradedFirst_range_eq_middle_ker,
    LinearMap.finrank_range_of_inj (frameGradedFirst_injective d),
    four_variable_homogeneous_finrank]

lemma frameGradedMiddle_range_finrank (d : ℕ) :
    finrank K (LinearMap.range (frameGradedMiddle (K := K) (d+2))) + (d+3).choose 3 =
      5 * (d+5).choose 3 := by
  have h := (frameGradedMiddle (K := K) (d+2)).finrank_range_add_finrank_ker
  rw [frameGradedMiddle_ker_finrank, frameHomogeneousVector_finrank] at h
  simpa only [Nat.add_assoc] using h

lemma frameGradedMiddle_range_finrank_low (d : ℕ) (hd : d < 2) :
    finrank K (LinearMap.range (frameGradedMiddle (K := K) d)) =
      5 * (d+3).choose 3 := by
  rw [LinearMap.finrank_range_of_inj (frameGradedMiddle_injective_low d hd),
    frameHomogeneousVector_finrank]

end
end PfaffianDescent
