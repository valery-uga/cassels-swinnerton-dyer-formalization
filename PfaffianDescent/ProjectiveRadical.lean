import AllCharacteristics.CoordinateCharts
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Finiteness.Ideal

namespace PfaffianDescent
open AllCharacteristics.HomogeneousProjective
section
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (𝒜 : ℕ → Submodule K A) [GradedRing 𝒜]

/-- A homogeneous ideal with empty projective zero locus contains the
irrelevant ideal after taking radicals. -/
theorem irrelevant_le_radical_of_empty_projective_zeroLocus
    (J : HomogeneousIdeal 𝒜)
    (hJ : ∀ x : ProjectiveSpectrum 𝒜, ¬ J ≤ x.asHomogeneousIdeal) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ J.toIdeal.radical := by
  rw [J.isHomogeneous.radical_eq]
  apply le_sInf
  rintro P ⟨hP, hJP, hprime⟩
  by_contra h
  exact hJ ⟨⟨P, hP⟩, hprime, h⟩ hJP

/-- If a homogeneous linear form vanishes nowhere on Proj, some power of
its irrelevant ideal is contained in the principal ideal of the form. -/
theorem irrelevant_pow_le_span_of_nowhere_vanishing
    (hfg : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.FG) (z : A) (hz : z ∈ 𝒜 1)
    (hnz : ∀ x : ProjectiveSpectrum 𝒜, z ∉ x.asHomogeneousIdeal) :
    ∃ N : ℕ, (HomogeneousIdeal.irrelevant 𝒜).toIdeal ^ N ≤ Ideal.span {z} := by
  have hhom : (Ideal.span {z}).IsHomogeneous 𝒜 :=
    Ideal.homogeneous_span 𝒜 {z} (by
      intro a ha
      obtain rfl := Set.mem_singleton_iff.mp ha
      exact ⟨1, hz⟩)
  apply Ideal.exists_pow_le_of_le_radical_of_fg (I := (HomogeneousIdeal.irrelevant 𝒜).toIdeal)
    (J := Ideal.span {z}) ?_ hfg
  apply irrelevant_le_radical_of_empty_projective_zeroLocus 𝒜 ⟨_, hhom⟩
  intro x hx
  exact hnz x (hx (Ideal.subset_span (Set.mem_singleton z)))

end

section
variable {K : Type*} [CommRing K] {σ : Type} [Finite σ]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Degree at least `N` in a polynomial quotient belongs to the `N`th
power of its irrelevant ideal. -/
theorem quotient_grade_mem_irrelevant_pow
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (N n : ℕ) (hn : N ≤ n) {a : CoordinateRing I} (ha : a ∈ grading I n) :
    a ∈ (HomogeneousIdeal.irrelevant (grading I)).toIdeal ^ N := by
  obtain ⟨p, hp, rfl⟩ := ha
  have hvars : p ∈ MvPolynomial.idealOfVars σ K ^ N := by
    rw [MvPolynomial.mem_pow_idealOfVars_iff]
    intro m hm
    have he : m.degree = n := by
      simpa only [Finsupp.degree_apply] using
        (MvPolynomial.IsHomogeneous.degree_eq_sum_deg_support hp hm).symm
    exact he ▸ hn
  have hmap : (MvPolynomial.idealOfVars σ K).map (Ideal.Quotient.mk I.toIdeal) =
      (HomogeneousIdeal.irrelevant (grading I)).toIdeal := by
    rw [irrelevant_eq_coordinateIdeal, MvPolynomial.idealOfVars, Ideal.map_span]
    rw [← Set.range_comp]
    rfl
  rw [← hmap, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem (Ideal.Quotient.mk I.toIdeal) hvars

/-- A nowhere-vanishing degree-one element divides every sufficiently high
homogeneous element of a polynomial quotient. -/
theorem quotient_grade_eventually_mem_span
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule σ K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (hnz : ∀ x : ProjectiveSpectrum (grading I), z ∉ x.asHomogeneousIdeal) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ a ∈ grading I n, a ∈ Ideal.span {z} := by
  have hfg : (HomogeneousIdeal.irrelevant (grading I)).toIdeal.FG := by
    rw [irrelevant_eq_coordinateIdeal]
    exact Submodule.fg_span (Set.finite_range _)
  obtain ⟨N, hN⟩ := irrelevant_pow_le_span_of_nowhere_vanishing (grading I) hfg z hz hnz
  exact ⟨N, fun n hn a ha => hN (quotient_grade_mem_irrelevant_pow I N n hn ha)⟩

end
end PfaffianDescent
