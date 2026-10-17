import AllCharacteristics.RegularPairDimension

/-!
# Regular generators for a surface point ideal

A two-dimensional regular local ring has two generators of its maximal ideal
which also form a regular sequence. This is the local parameter input for
the point-supported Koszul resolution.
-/

namespace PfaffianDescent

open scoped nonZeroDivisors
open AllCharacteristics

set_option linter.style.haveILetI false in
/-- A regular local surface point has a regular pair generating its entire
maximal ideal, over an arbitrary residue field. -/
theorem exists_regular_pair_span_maximalIdeal_of_dim_two
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) :
    ∃ p q : R, p ∈ R⁰ ∧
      Ideal.Quotient.mk (Ideal.span {p}) q ∈ (R ⧸ Ideal.span {p})⁰ ∧
      Ideal.span ({p, q} : Set R) = IsLocalRing.maximalIdeal R := by
  obtain ⟨p, q, hp, hp_square, hq, hspan⟩ :=
    exists_pair_span_maximalIdeal_of_regularLocal_dim_two hdim
  letI : IsRegularLocalRing (R ⧸ Ideal.span {p}) :=
    isRegularLocalRing_quotient_parameter p hp hp_square
  letI : IsDomain R := isDomain_of_regularLocalRing R
  letI : IsDomain (R ⧸ Ideal.span {p}) :=
    isDomain_of_regularLocalRing (R ⧸ Ideal.span {p})
  refine ⟨p, q, ?_, ?_, ?_⟩
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hpzero
    apply hp_square
    rw [hpzero]
    exact (IsLocalRing.maximalIdeal R ^ 2).zero_mem
  · rw [mem_nonZeroDivisors_iff_ne_zero]
    intro hqzero
    have hpzero : Ideal.Quotient.mk (Ideal.span {p}) p = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.subset_span (by simp)
    have hmaxzero : IsLocalRing.maximalIdeal (R ⧸ Ideal.span {p}) = ⊥ := by
      rw [← IsLocalRing.map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk (Ideal.span {p})) Ideal.Quotient.mk_surjective,
        ← hspan, Ideal.map_sup, Ideal.map_span, Ideal.map_span]
      simp only [Set.image_singleton, hpzero, hqzero, Ideal.span_singleton_zero]
      simp
    have hzero := ringKrullDim_eq_zero_of_isField
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmaxzero)
    have hquotdim := ringKrullDim_quotient_parameter_add_one p hp hp_square
    rw [hzero, hdim] at hquotdim
    norm_num at hquotdim
  · simpa only [Ideal.span_insert, sup_comm] using hspan

end PfaffianDescent
