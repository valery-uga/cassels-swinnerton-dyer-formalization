import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Homogeneous separation of relevant prime ideals

A relevant homogeneous prime can be avoided by a homogeneous element of
positive degree. Finitely many homogeneous ideals not contained in that prime
can simultaneously be made to contain such an element. These are the
constructive ingredients for a common affine neighborhood of finitely many
points of an actual projective spectrum.
-/

open AlgebraicGeometry
namespace AllCharacteristics
universe u v w
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Noncontainment of homogeneous ideals is witnessed by a homogeneous element. -/
theorem exists_homogeneous_mem_not_mem (I J : HomogeneousIdeal 𝒜) (h : ¬ I ≤ J) :
    ∃ (d : ℕ) (a : A), a ∈ 𝒜 d ∧ a ∈ I ∧ a ∉ J := by
  classical
  obtain ⟨a, haI, haJ⟩ := Set.not_subset.mp h
  have hn : ¬ ∀ d, (DirectSum.decompose 𝒜 a d : A) ∈ J :=
    fun hh ↦ haJ (J.isHomogeneous.mem_iff.mpr hh)
  obtain ⟨d, hd⟩ := not_forall.mp hn
  exact ⟨d, _, (DirectSum.decompose 𝒜 a d).property, I.isHomogeneous.mem_iff.mp haI d, hd⟩

/-- Every actual projective-spectrum point admits a positive-degree homogeneous
nonvanishing element. -/
theorem exists_positive_homogeneous_not_mem (p : ProjectiveSpectrum 𝒜) :
    ∃ (d : ℕ), 0 < d ∧ ∃ a : A, a ∈ 𝒜 d ∧ a ∉ p.asHomogeneousIdeal := by
  classical
  by_contra! h
  apply p.not_irrelevant_le
  change (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ p.asHomogeneousIdeal.toIdeal
  apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
  intro d hd a ha
  exact h d hd a ha

/-- Finitely many homogeneous ideals not contained in a relevant prime have a
common positive-degree homogeneous element outside that prime. -/
theorem exists_positive_homogeneous_prime_separator {ι : Type w}
    (p : ProjectiveSpectrum 𝒜) (I : ι → HomogeneousIdeal 𝒜) (s : Finset ι)
    (h : ∀ i ∈ s, ¬ I i ≤ p.asHomogeneousIdeal) :
    ∃ (d : ℕ), 0 < d ∧ ∃ a : A,
      a ∈ 𝒜 d ∧ a ∉ p.asHomogeneousIdeal ∧ ∀ i ∈ s, a ∈ I i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨d, hd, a, ha, hp⟩ := exists_positive_homogeneous_not_mem 𝒜 p
    exact ⟨d, hd, a, ha, hp, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨d, hd, a, ha, hp, hs⟩ := ih (fun j hj ↦ h j (Finset.mem_insert_of_mem hj))
    obtain ⟨e, b, hb, hbI, hbp⟩ := exists_homogeneous_mem_not_mem 𝒜 (I i)
      p.asHomogeneousIdeal (h i (Finset.mem_insert_self i s))
    refine ⟨e + d, Nat.add_pos_right e hd, b * a, SetLike.mul_mem_graded hb ha, ?_, ?_⟩
    · intro hba
      exact (p.isPrime.mem_or_mem hba).elim hbp hp
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (I j).toIdeal.mul_mem_right a hbI
      · exact (I j).toIdeal.mul_mem_left b (hs j hj)

end AllCharacteristics
