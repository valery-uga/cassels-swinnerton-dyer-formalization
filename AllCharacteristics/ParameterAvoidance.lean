import AllCharacteristics.RegularLocalLowDimension
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Choosing a parameter away from the minimal primes

Prime avoidance allows one nonprime exceptional ideal, here `m²`. Consequently
this choice works over finite residue fields as well as infinite ones.
-/

namespace AllCharacteristics
open IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A positive-dimensional Noetherian local ring admits an element of `m` that
is outside `m²` and outside every minimal prime. No residue-field cardinality
assumption is made. -/
theorem exists_parameter_avoiding_minimal_primes (hd : ringKrullDim R ≠ 0) :
    ∃ x ∈ maximalIdeal R, x ∉ maximalIdeal R ^ 2 ∧
      ∀ p ∈ minimalPrimes R, x ∉ p := by
  classical
  let m := maximalIdeal R
  have hmin : m ∉ minimalPrimes R := by
    intro h
    have hh := Ideal.height_eq_zero_iff.mpr h
    apply hd
    rw [← maximalIdeal_height_eq_ringKrullDim]
    exact_mod_cast hh
  have hsq : m ≠ m ^ 2 := by
    intro hh
    have hi : IsIdempotentElem m := by
      change m * m = m
      simpa only [pow_two] using hh.symm
    rcases (Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing m).mp hi with hbot | htop
    · exact hd (ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr hbot))
    · exact (maximalIdeal.isMaximal R).ne_top htop
  let s : Set (Ideal R) := insert (m ^ 2) (minimalPrimes R)
  have hs : s.Finite := (minimalPrimes.finite_of_isNoetherianRing (R := R)).insert _
  have hms : m ∉ s := by
    intro h
    exact (Set.mem_insert_iff.mp h).elim hsq hmin
  have hsqtop : m ^ 2 ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top (Ideal.pow_le_self (by decide))
  have hp : ∀ I ∈ s, I ≠ m ^ 2 → I ≠ m ^ 2 → I.IsPrime := by
    intro I hI hne _
    rcases Set.mem_insert_iff.mp hI with he | hm
    · exact (hne he).elim
    · exact hm.isPrime
  have hn : ¬ ((m : Set R) ⊆ ⋃ I ∈ s, (I : Set R)) := by
    rw [Ideal.subset_iUnion_iff_mem_of_isMaximal_of_finite hs (m ^ 2) (m ^ 2) hp hsqtop hsqtop]
    exact hms
  obtain ⟨x, hx, hxn⟩ := Set.not_subset.mp hn
  refine ⟨x, hx, ?_, ?_⟩
  · intro h
    apply hxn
    exact Set.mem_iUnion₂.mpr ⟨m ^ 2, Set.mem_insert _ _, h⟩
  · intro p hp h
    apply hxn
    exact Set.mem_iUnion₂.mpr ⟨p, Set.mem_insert_of_mem _ hp, h⟩

end AllCharacteristics
