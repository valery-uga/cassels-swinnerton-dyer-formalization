import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

namespace PfaffianDescent
open HomogeneousLocalization
section
variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : Function.Surjective f)
include hf

/-- A homogeneous element lifts homogeneously under a surjective graded map. -/
theorem gradedSurjective_homogeneous_lift (n : ℕ) (b : B) (hb : b ∈ ℬ n) :
    ∃ a : A, a ∈ 𝒜 n ∧ f a = b := by
  obtain ⟨a, ha⟩ := hf b
  refine ⟨DirectSum.decompose 𝒜 a n, (DirectSum.decompose 𝒜 a n).2, ?_⟩
  rw [f.map_directSumDecompose, ha, DirectSum.decompose_of_mem_same ℬ hb]

/-- Surjectivity gives the irrelevant-ideal condition needed for `Proj.map`. -/
theorem gradedSurjective_irrelevant_le :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  apply (HomogeneousIdeal.irrelevant_le ℬ).mpr
  intro n hn b hb
  obtain ⟨a, ha, rfl⟩ := gradedSurjective_homogeneous_lift f hf n b hb
  exact Ideal.mem_map_of_mem f (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn ha)

/-- A surjective graded map surjects on every corresponding homogeneous
localization, hence on every projective affine chart. -/
theorem gradedSurjective_awayMap (s : A) {d : ℕ} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro x
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.2 hs) x
  obtain ⟨a, ha, rfl⟩ := gradedSurjective_homogeneous_lift f hf (n • d) b hb
  exact ⟨Away.mk 𝒜 hs n a ha, Away.map_mk f s hs n a ha⟩

end
end PfaffianDescent
