import PfaffianDescent.NativeArtinianObstructionLocal316
import Mathlib.RingTheory.Filtration

/-! Krull separation for the concrete finite-length obstruction tests. -/
namespace PfaffianDescent
open IsLocalRing

variable {P : Type*} [CommRing P] [IsLocalRing P] [IsNoetherianRing P]

theorem obstruction_exists_power_not_mem316 (J : Ideal P)
    (hJ : J ≤ maximalIdeal P) {x : P} (hx : x ∉ J) :
    ∃ N : ℕ, x ∉ J ⊔ maximalIdeal P ^ N := by
  letI : IsLocalRing (P ⧸ J) := obstructionQuotient_local316 J hJ
  letI : IsNoetherianRing (P ⧸ J) :=
    isNoetherianRing_of_surjective P (P ⧸ J) (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
  by_contra h
  push Not at h
  have hall : Ideal.Quotient.mk J x ∈
      (⨅ N : ℕ, maximalIdeal (P ⧸ J) ^ N) := by
    apply Ideal.mem_iInf.mpr
    intro N
    have hm := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) (h N)
    rw [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq, Ideal.map_pow,
      IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
        Ideal.Quotient.mk_surjective] at hm
    exact hm
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top] at hall
  exact hx ((Ideal.Quotient.eq_zero_iff_mem).1 hall)

theorem obstruction_exists_positive_power_not_mem316 (J : Ideal P)
    (hJ : J ≤ maximalIdeal P) {x : P} (hx : x ∉ J) :
    ∃ N : ℕ, 0 < N ∧ x ∉ J ⊔ maximalIdeal P ^ N := by
  obtain ⟨N, hN⟩ := obstruction_exists_power_not_mem316 J hJ hx
  have hle : J ⊔ maximalIdeal P ^ (N + 1) ≤ J ⊔ maximalIdeal P ^ N :=
    sup_le_sup le_rfl (Ideal.pow_le_pow_right (Nat.le_succ N))
  exact ⟨N + 1, Nat.zero_lt_succ N, fun h => hN (hle h)⟩

theorem obstruction_exists_detecting_quotient316 (I : Ideal P) {x : P}
    (hx : x ∉ maximalIdeal P * I) :
    ∃ N : ℕ, 0 < N ∧
      Ideal.Quotient.mk (obstructionThickIdeal316 (maximalIdeal P) I N) x ≠ 0 := by
  obtain ⟨N, hN, hxN⟩ := obstruction_exists_positive_power_not_mem316
    (maximalIdeal P * I) Ideal.mul_le_left hx
  exact ⟨N, hN, obstructionQuotient_relation_nonzero316 _ _ _ hxN⟩

end PfaffianDescent
