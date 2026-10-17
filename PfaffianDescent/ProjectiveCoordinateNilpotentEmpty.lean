import AllCharacteristics.CoordinateCharts
import PfaffianDescent.ProjectiveRadical

/-!
# Algebraic certificates for an empty projective quotient

If every homogeneous coordinate becomes nilpotent in a polynomial quotient,
every homogeneous prime contains the irrelevant ideal. Hence the projective
spectrum is empty. This gives a finite algebraic target for checking that a
specialized Voisin Jacobian singular fibre is empty.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem isEmpty_projectiveScheme_of_nilpotent_coordinates
    {R : Type u} [CommRing R] {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (homogeneousSubmodule σ R))
    (h : ∀ j : σ, ∃ n : ℕ, coordinate I j ^ n = 0) :
    IsEmpty (scheme I) := by
  change IsEmpty (ProjectiveSpectrum (grading I))
  refine ⟨fun x => ?_⟩
  apply x.not_irrelevant_le
  apply toIdeal_le_toIdeal_iff.mp
  rw [irrelevant_eq_coordinateIdeal]
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  obtain ⟨n, hn⟩ := h j
  apply x.isPrime.mem_of_pow_mem n
  rw [hn]
  exact (x.asHomogeneousIdeal.toIdeal).zero_mem

/-- A finite list of power-membership certificates in the original
homogeneous polynomial ideal makes its projective quotient empty. -/
theorem isEmpty_projectiveScheme_of_coordinate_powers_mem
    {R : Type u} [CommRing R] {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (homogeneousSubmodule σ R))
    (h : ∀ j : σ, ∃ n : ℕ, (MvPolynomial.X j : MvPolynomial σ R) ^ n ∈ I.toIdeal) :
    IsEmpty (scheme I) := by
  apply isEmpty_projectiveScheme_of_nilpotent_coordinates I
  intro j
  obtain ⟨n, hn⟩ := h j
  refine ⟨n, ?_⟩
  change (Ideal.Quotient.mk I.toIdeal (MvPolynomial.X j)) ^ n = 0
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hn

/-- Emptiness of a projective polynomial quotient is witnessed by finite
coordinate-power memberships in its homogeneous ideal. -/
theorem coordinate_powers_mem_of_isEmpty_projectiveScheme
    {R : Type u} [CommRing R] {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (homogeneousSubmodule σ R))
    (h : IsEmpty (scheme I)) :
    ∀ j : σ, ∃ n : ℕ,
      (MvPolynomial.X j : MvPolynomial σ R) ^ n ∈ I.toIdeal := by
  change IsEmpty (ProjectiveSpectrum (grading I)) at h
  letI := h
  let J : HomogeneousIdeal (grading I) := ⊥
  have hrad : (HomogeneousIdeal.irrelevant (grading I)).toIdeal ≤
      J.toIdeal.radical :=
    irrelevant_le_radical_of_empty_projective_zeroLocus
      (grading I) J (fun x _ => isEmptyElim x)
  intro j
  have hcoord : coordinate I j ∈
      (HomogeneousIdeal.irrelevant (grading I)).toIdeal := by
    rw [irrelevant_eq_coordinateIdeal]
    exact Ideal.subset_span (Set.mem_range_self j)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hrad hcoord)
  refine ⟨n, ?_⟩
  have hzero : (coordinate I j) ^ n = 0 := by
    change (coordinate I j) ^ n ∈ (⊥ : Ideal (CoordinateRing I)) at hn
    exact (Ideal.mem_bot).mp hn
  change (Ideal.Quotient.mk I.toIdeal (MvPolynomial.X j)) ^ n = 0 at hzero
  rw [← map_pow] at hzero
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

/-- The finite coordinate-power test characterizes emptiness of the
projective scheme, with no algebraic-closedness assumption on the base ring. -/
theorem isEmpty_projectiveScheme_iff_coordinate_powers_mem
    {R : Type u} [CommRing R] {σ : Type} [Finite σ]
    (I : HomogeneousIdeal (homogeneousSubmodule σ R)) :
    IsEmpty (scheme I) ↔
      ∀ j : σ, ∃ n : ℕ,
        (MvPolynomial.X j : MvPolynomial σ R) ^ n ∈ I.toIdeal := by
  constructor
  · exact coordinate_powers_mem_of_isEmpty_projectiveScheme I
  · exact isEmpty_projectiveScheme_of_coordinate_powers_mem I

end PfaffianDescent
