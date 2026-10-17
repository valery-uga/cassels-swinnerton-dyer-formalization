import PfaffianDescent.FrameHomogeneousMaps

namespace PfaffianDescent
open MvPolynomial Module
open scoped BigOperators
section
variable {K : Type*} [Field K]

lemma frameLastMap_component (d : ℕ) (v : Fin 5 → MvPolynomial (Fin 4) K) :
    frameLastMap (fun i => homogeneousComponent d (v i)) =
      homogeneousComponent (d+2) (frameLastMap v) := by
  change (∑ i, homogeneousComponent d (v i) * frameRelations i) =
    homogeneousComponent (d+2) (∑ i, v i * frameRelations i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (homogeneousComponent_mul_right (frameRelations_homogeneous i) d).symm

lemma frameGradedLast_range_iff (d : ℕ) (p : FrameHomogeneous K (d+2)) :
    p ∈ LinearMap.range (frameGradedLast d) ↔ p.val ∈ frameIdeal := by
  constructor
  · rintro ⟨v, rfl⟩
    rw [← frameLastMap_range]
    exact ⟨frameVectorInclusion d v, rfl⟩
  · intro hp
    rw [← frameLastMap_range] at hp
    obtain ⟨v, hv⟩ := hp
    let w : Fin 5 → FrameHomogeneous K d := fun i =>
      ⟨homogeneousComponent d (v i), homogeneousComponent_mem d (v i)⟩
    refine ⟨w, Subtype.ext ?_⟩
    change frameLastMap (fun i => homogeneousComponent d (v i)) = p.val
    rw [frameLastMap_component, hv, homogeneousComponent_eq_self p.property]

noncomputable def frameGradedAugmentation (d : ℕ) :
    FrameHomogeneous K d →ₗ[K] FrameCoordinateRing.component (K := K) d :=
  ((Ideal.Quotient.mkₐ K (frameIdeal (K := K))).toLinearMap.comp
    (FrameHomogeneous K d).subtype).codRestrict _ (fun p => ⟨p.val, p.property, rfl⟩)

lemma frameGradedAugmentation_surjective (d : ℕ) :
    Function.Surjective (frameGradedAugmentation (K := K) d) := by
  rintro ⟨p, hp⟩
  obtain ⟨r, hr, he⟩ := hp
  exact ⟨⟨r, hr⟩, Subtype.ext he⟩

lemma frameGradedAugmentation_ker (d : ℕ) :
    LinearMap.ker (frameGradedAugmentation (K := K) (d+2)) =
      LinearMap.range (frameGradedLast d) := by
  ext p
  rw [frameGradedLast_range_iff, LinearMap.mem_ker]
  constructor
  · intro h
    exact Ideal.Quotient.eq_zero_iff_mem.mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr h)

/-- The image of the quadratic-generator map has codimension five in every degree. -/
theorem frameGradedLast_range_finrank (d : ℕ) :
    finrank K (LinearMap.range (frameGradedLast (K := K) d)) + 5 =
      (d+5).choose 3 := by
  have h := (frameGradedAugmentation (K := K) (d+2)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (frameGradedAugmentation_surjective (d+2)),
    finrank_top, FrameCoordinateRing.hilbert_high, frameGradedAugmentation_ker,
    four_variable_homogeneous_finrank] at h
  simpa only [Nat.add_assoc, Nat.add_comm 5] using h

/-- The dimension identity for the kernel of the last free-module map. -/
theorem frameGradedLast_ker_finrank (d : ℕ) :
    finrank K (LinearMap.ker (frameGradedLast (K := K) d)) + (d+5).choose 3 =
      5 * (d+3).choose 3 + 5 := by
  have h := (frameGradedLast (K := K) d).finrank_range_add_finrank_ker
  rw [frameHomogeneousVector_finrank] at h
  have h' := frameGradedLast_range_finrank (K := K) d
  omega

end
end PfaffianDescent
