import AllCharacteristics.RegularLocalDomain
import AllCharacteristics.ParameterAvoidance
import Mathlib.Data.Finset.Card

/-!
# Own minimal parameter pair avoiding a height-one prime

Two-ideal avoidance chooses x outside BOTH P and m², over any residue field.
Existing actual regular-parameter/domain theorems make (x) prime. A minimal
maximal-ideal generating set containing x supplies y. Neither parameter,
parameter primality, regular quotient, nor pair relation is supplied.
SOURCE ONLY / UNVERIFIED; root owns compiler/audit.
-/
noncomputable section
namespace PfaffianDescent.Coray
open IsLocalRing
universe u
variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A height-one prime in an actual two-dimensional regular local ring has
an OWN minimal maximal-ideal pair whose first prime parameter avoids P. -/
theorem regularLocal_dimension_two_exists_parameter_pair_avoiding_heightOnePrime
    (hdim : ringKrullDim R = 2) (P : Ideal R) [P.IsPrime]
    (hheight : P.height = 1) :
    ∃ x y : R, x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧
      maximalIdeal R = Ideal.span ({x, y} : Set R) ∧ x ∉ P ∧
      (Ideal.span ({x} : Set R)).IsPrime ∧ y ∉ Ideal.span ({x} : Set R) := by
  classical
  have hdim0 : ringKrullDim R ≠ 0 := by rw [hdim]; norm_num
  have hPm : P ≠ maximalIdeal R := by
    intro he
    have hbad : (1 : WithBot ℕ∞) = 2 := by
      calc
        (1 : WithBot ℕ∞) = (P.height : WithBot ℕ∞) := by rw [hheight, WithBot.coe_one]
        _ = ringKrullDim R := by rw [he]; exact maximalIdeal_height_eq_ringKrullDim
        _ = 2 := hdim
    norm_num at hbad
  have hPrime : P.IsPrime := inferInstance
  have hmP : ¬ maximalIdeal R ≤ P := by
    intro h
    exact hPm (le_antisymm (le_maximalIdeal hPrime.ne_top) h)
  have hmSq : ¬ maximalIdeal R ≤ maximalIdeal R ^ 2 := by
    obtain ⟨z, hz, hzn, _⟩ := AllCharacteristics.exists_parameter_avoiding_minimal_primes hdim0
    intro h
    exact hzn (h hz)
  have hnot : ¬ (maximalIdeal R : Set R) ⊆
      (P : Set R) ∪ ((maximalIdeal R ^ 2 : Ideal R) : Set R) := by
    rw [Ideal.subset_union]
    exact not_or.mpr ⟨hmP, hmSq⟩
  obtain ⟨x, hx, hxn⟩ := Set.not_subset.mp hnot
  have hxP : x ∉ P := fun h => hxn (Or.inl h)
  have hxSq : x ∉ maximalIdeal R ^ 2 := fun h => hxn (Or.inr h)
  have hprime := AllCharacteristics.isPrime_span_parameter x hx hxSq
  obtain ⟨s, hxs, hcard, hspan⟩ := AllCharacteristics.exists_minimal_generators_containing x hx hxSq
  have hrank : (maximalIdeal R).spanFinrank = 2 := by
    exact_mod_cast (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).trans hdim
  have hcard2 : s.card = 2 := hcard.trans hrank
  have herase : (s.erase x).card = 1 := by
    have heq := Finset.card_erase_add_one hxs
    omega
  obtain ⟨y, hyset⟩ := Finset.card_eq_one.mp herase
  have hs : s = {x, y} := by rw [← Finset.insert_erase hxs, hyset]
  have hpair : maximalIdeal R = Ideal.span ({x, y} : Set R) := by
    simpa only [hs, Finset.coe_insert, Finset.coe_singleton] using hspan.symm
  have hy : y ∈ maximalIdeal R := by
    rw [hpair]
    exact Ideal.subset_span (Set.mem_insert_of_mem x (Set.mem_singleton y))
  have hynot : y ∉ Ideal.span ({x} : Set R) := by
    intro hyin
    have hmEq : maximalIdeal R = Ideal.span ({x} : Set R) := by
      rw [hpair, Ideal.span_pair_eq_span_left_iff_dvd]
      exact Ideal.mem_span_singleton.mp hyin
    have hbound : (maximalIdeal R).spanFinrank ≤ 1 := by
      rw [hmEq]
      simpa only [Set.ncard_singleton] using
        Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)
    omega
  exact ⟨x, y, hx, hy, hpair, hxP, hprime, hynot⟩

end PfaffianDescent.Coray
