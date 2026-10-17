import PfaffianDescent.FrameGradedAugmentation
import PfaffianDescent.FrameGradedKernel
import PfaffianDescent.FrameDimensionIdentity

namespace PfaffianDescent
open Module
section
variable {K : Type*} [Field K]

lemma frameGradedMiddle_exact_high (d : ℕ) :
    LinearMap.range (frameGradedMiddle (K := K) (d+2)) =
      LinearMap.ker (frameGradedLast (d+3)) := by
  apply Submodule.eq_of_le_of_finrank_eq (frameGradedMiddle_range_le (d+2))
  change finrank K (LinearMap.range (frameGradedMiddle (K := K) (d+2))) =
    finrank K (LinearMap.ker (frameGradedLast (K := K) (d+3)))
  have hm := frameGradedMiddle_range_finrank (K := K) d
  have hk := frameGradedLast_ker_finrank (K := K) (d+3)
  have hi := frame_dimension_identity d
  change finrank K (LinearMap.ker (frameGradedLast (K := K) (d+3))) + (d+8).choose 3 =
    5 * (d+6).choose 3 + 5 at hk
  omega

lemma frameGradedMiddle_exact_low (d : ℕ) (hd : d < 2) :
    LinearMap.range (frameGradedMiddle (K := K) d) =
      LinearMap.ker (frameGradedLast (d+1)) := by
  apply Submodule.eq_of_le_of_finrank_eq (frameGradedMiddle_range_le d)
  have hm := frameGradedMiddle_range_finrank_low (K := K) d hd
  have hk := frameGradedLast_ker_finrank (K := K) (d+1)
  interval_cases d <;> norm_num [Nat.choose] at hm hk ⊢ <;> omega

/-- Middle exactness in every positive homogeneous degree. -/
theorem frameGradedMiddle_exact (d : ℕ) :
    LinearMap.range (frameGradedMiddle (K := K) d) =
      LinearMap.ker (frameGradedLast (d+1)) := by
  rcases d with _ | _ | d
  · exact frameGradedMiddle_exact_low 0 (by decide)
  · exact frameGradedMiddle_exact_low 1 (by decide)
  · exact frameGradedMiddle_exact_high d

lemma frameGradedLast_ker_zero : LinearMap.ker (frameGradedLast (K := K) 0) = ⊥ := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq bot_le
  have hk := frameGradedLast_ker_finrank (K := K) 0
  change finrank K (LinearMap.ker (frameGradedLast (K := K) 0)) + 10 = 10 at hk
  rw [finrank_bot]
  omega

end
end PfaffianDescent
