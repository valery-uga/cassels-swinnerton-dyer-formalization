import AllCharacteristics.HomogeneousPrimeAvoidance
import Mathlib.Order.Preorder.Finite

/-!
# Homogeneous avoidance of arbitrary finite families of relevant primes

Passing to the maximal ideals in a finite family produces an antichain.
The proved homogeneous separator for that antichain avoids every original
prime, because every member lies below one of these maximal members.
-/

open AlgebraicGeometry
namespace AllCharacteristics
universe u v
variable {A : Type u} [CommRing A] {σ : Type v} [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Every finite family of relevant homogeneous primes admits one homogeneous
element of positive degree outside all of them. -/
theorem exists_positive_homogeneous_avoiding_finite_primes
    (s : Finset (HomogeneousIdeal 𝒜))
    (hprime : ∀ I ∈ s, I.toIdeal.IsPrime)
    (hrel : ∀ I ∈ s, ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ I) :
    ∃ (d : ℕ), 0 < d ∧ ∃ a : A, a ∈ 𝒜 d ∧ ∀ I ∈ s, a ∉ I := by
  classical
  let t := s.filter (fun I ↦ Maximal (· ∈ s) I)
  let p (i : t) : ProjectiveSpectrum 𝒜 := {
    asHomogeneousIdeal := i.val
    isPrime := hprime i.val (Finset.mem_filter.mp i.property).1
    not_irrelevant_le := hrel i.val (Finset.mem_filter.mp i.property).1 }
  have hp : ∀ i j : t, i ≠ j → ¬ (p i).asHomogeneousIdeal ≤ (p j).asHomogeneousIdeal := by
    intro i j hij hle
    have hi : Maximal (· ∈ s) i.val := (Finset.mem_filter.mp i.property).2
    have hj : j.val ∈ s := (Finset.mem_filter.mp j.property).1
    apply hij
    apply Subtype.ext
    exact le_antisymm hle (hi.2 hj hle)
  obtain ⟨d, hd, a, ha, hn⟩ := exists_positive_homogeneous_avoiding_antichain 𝒜 p hp
  refine ⟨d, hd, a, ha, ?_⟩
  intro I hI haI
  obtain ⟨J, hIJ, hJ⟩ := s.exists_le_maximal hI
  let j : t := ⟨J, Finset.mem_filter.mpr ⟨hJ.prop, hJ⟩⟩
  exact hn j (hIJ haI)

/-- Any finite set of actual projective-spectrum points is contained in one
positive-degree homogeneous basic open. -/
theorem exists_positive_homogeneous_avoiding_projective_points
    (s : Finset (ProjectiveSpectrum 𝒜)) :
    ∃ (d : ℕ), 0 < d ∧ ∃ a : A, a ∈ 𝒜 d ∧ ∀ p ∈ s, a ∉ p.asHomogeneousIdeal := by
  classical
  let t := s.image ProjectiveSpectrum.asHomogeneousIdeal
  have hp : ∀ I ∈ t, I.toIdeal.IsPrime := by
    intro I hI
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hI
    exact p.isPrime
  have hr : ∀ I ∈ t, ¬ HomogeneousIdeal.irrelevant 𝒜 ≤ I := by
    intro I hI
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hI
    exact p.not_irrelevant_le
  obtain ⟨d, hd, a, ha, hn⟩ := exists_positive_homogeneous_avoiding_finite_primes 𝒜 t hp hr
  exact ⟨d, hd, a, ha, fun p hp ↦ hn p.asHomogeneousIdeal (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩

end AllCharacteristics
