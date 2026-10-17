import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.Algebra.CharP.Basic

/-!
# Complete mixed-characteristic lifting bases for perfect fields

For a perfect field of positive characteristic, the Witt vectors supply an
actual complete DVR of characteristic zero with the prescribed residue field.
This constructs the lifting base in this case; it does not assume such a ring
exists and does not impose separability conditions on later finite points.
-/

open IsLocalRing
namespace AllCharacteristics
universe u v

/-- A domain mapping to a field of characteristic p has characteristic zero
if p itself remains nonzero in the domain. -/
theorem charZero_of_residue_prime_nonzero
    {R : Type u} {k : Type v} [CommRing R] [IsDomain R] [Field k]
    (p : ℕ) [hp : Fact p.Prime] [CharP k p] (b : R →+* k) (hne : (p : R) ≠ 0) :
    CharZero R := by
  apply (CharZero.charZero_iff_forall_prime_ne_zero R).mpr
  intro l hl hz
  have hk : (l : k) = 0 := by simpa only [map_natCast, map_zero] using congrArg b hz
  have hdiv : p ∣ l := (CharP.cast_eq_zero_iff k p l).mp hk
  have hpl : p = l := ((Nat.dvd_prime hl).mp hdiv).resolve_left hp.out.ne_one
  exact hne (hpl.symm ▸ hz)

/-- Witt vectors over a field of positive characteristic have characteristic
zero, as the characteristic prime is nonzero in the Witt ring. -/
theorem wittVector_charZero
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] :
    CharZero (WittVector p k) :=
  charZero_of_residue_prime_nonzero p WittVector.constantCoeff (WittVector.p_nonzero p k)

/-- The Witt ring of a perfect field is complete for its maximal ideal. -/
theorem wittVector_isAdicComplete_maximalIdeal
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p] :
    IsAdicComplete (maximalIdeal (WittVector p k)) (WittVector p k) := by
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer (p : WittVector p k)).mp
    (WittVector.irreducible p)]
  infer_instance

/-- Every perfect field of positive characteristic is the exact residue field
of a constructed complete DVR of characteristic zero, with p as uniformizer. -/
theorem exists_completeDVR_of_perfect_field
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p] :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : IsAdicComplete (maximalIdeal R) R) (_ : CharZero R) (b : R →+* k),
      Function.Surjective b ∧ maximalIdeal R = Ideal.span {(p : R)} := by
  have := wittVector_charZero p k
  have := wittVector_isAdicComplete_maximalIdeal p k
  exact ⟨WittVector p k, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, WittVector.constantCoeff, WittVector.constantCoeff_surjective p,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer (p : WittVector p k)).mp
      (WittVector.irreducible p)⟩

end AllCharacteristics
