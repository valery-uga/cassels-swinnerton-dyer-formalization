import AllCharacteristics.GradedChartOverlap

/- SOURCE ONLY / UNVERIFIED. Actual degree-two fraction transition in the
TRUE homogeneous product-chart ring. No coordinate-transition certificate. -/
noncomputable section
namespace AllCharacteristics.GradedChart
open HomogeneousLocalization
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedRing G]
  {f g : A} (hf : f ∈ G 1) (hg : g ∈ G 1)

theorem quadratic_normalized_overlap_mul
    (Q : A) (hQ : Q ∈ G 2) :
    awayMap G hg rfl (Away.mk G hf 2 Q hQ) =
      (awayMap G hg rfl (normalized G hf g hg)) ^ 2 *
        awayMap G hf (mul_comm f g) (Away.mk G hg 2 Q hQ) := by
  apply val_injective
  simp only [pow_two, val_mul, val_awayMap_normalized,
    awayMap_mk, Away.val_mk, Localization.mk_mul]
  apply Localization.mk_eq_mk_iff.mpr
  rw [Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring

end AllCharacteristics.GradedChart
