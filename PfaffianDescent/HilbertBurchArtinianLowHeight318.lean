import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Ideal.Height
import Mathlib.Tactic.NormNum

/-!
An arbitrary finite-colength ideal is the unit ideal at every low-height prime.
-/

namespace AllCharacteristics.HilbertSurfaceDraft

/-- An Artinian quotient on a local surface has no support at a prime of
height at most one.  No regularity or complete-intersection premise is used. -/
theorem not_le_prime_height_le_one_of_artinian_quotient
    {R : Type*} [CommRing R] [IsLocalRing R]
    (hdim : ringKrullDim R = 2) (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] (p : Ideal R) [hp : p.IsPrime]
    (hpheight : p.height ≤ 1) : ¬ I ≤ p := by
  intro hIp
  obtain ⟨n, hn⟩ :=
    IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient I
  have hmp : IsLocalRing.maximalIdeal R ≤ p :=
    Ideal.IsPrime.le_of_pow_le (hn.trans hIp)
  have hpm : p ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal hp.ne_top
  have hpeq : p = IsLocalRing.maximalIdeal R := le_antisymm hpm hmp
  have hpdim : (p.height : WithBot ℕ∞) = ringKrullDim R := by
    rw [hpeq]
    exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  have hle : (p.height : WithBot ℕ∞) ≤ 1 := by exact_mod_cast hpheight
  rw [hpdim, hdim] at hle
  norm_num at hle

end AllCharacteristics.HilbertSurfaceDraft
