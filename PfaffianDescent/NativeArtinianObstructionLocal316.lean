import PfaffianDescent.NativeArtinianObstructionQuotient316
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! Local Artinian test rings for the concrete cotangent obstruction quotient.
No infinitesimal lifting or smoothness conclusion is assumed. -/
namespace PfaffianDescent
open IsLocalRing

variable {P : Type*} [CommRing P] [IsLocalRing P]

theorem obstructionQuotient_local316 (J : Ideal P) (hJ : J ≤ maximalIdeal P) :
    IsLocalRing (P ⧸ J) := by
  have hne : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal P).ne_top hJ
  letI : Nontrivial (P ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

theorem obstructionQuotient_artinian316 [IsNoetherianRing P]
    (J : Ideal P) (hJ : J ≤ maximalIdeal P) (N : ℕ) (hN : maximalIdeal P ^ N ≤ J) :
    IsArtinianRing (P ⧸ J) := by
  letI : IsLocalRing (P ⧸ J) := obstructionQuotient_local316 J hJ
  letI : IsNoetherianRing (P ⧸ J) :=
    isNoetherianRing_of_surjective P (P ⧸ J) (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  apply (isArtinianRing_iff_isNilpotent_maximalIdeal (P ⧸ J)).2
  refine ⟨N, ?_⟩
  rw [← IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective, ← Ideal.map_pow]
  exact Ideal.map_mk_eq_bot_of_le hN

theorem obstructionThinIdeal_le_maximal316 (I : Ideal P)
    (hI : I ≤ maximalIdeal P) (N : ℕ) (hN : 0 < N) :
    obstructionThinIdeal316 (maximalIdeal P) I N ≤ maximalIdeal P :=
  sup_le hI (Ideal.pow_le_self (Nat.ne_of_gt hN))

theorem obstructionThickIdeal_le_maximal316 (I : Ideal P)
    (hI : I ≤ maximalIdeal P) (N : ℕ) (hN : 0 < N) :
    obstructionThickIdeal316 (maximalIdeal P) I N ≤ maximalIdeal P :=
  (obstructionThickIdeal_le_thin316 _ _ _).trans
    (obstructionThinIdeal_le_maximal316 I hI N hN)

theorem obstructionThickQuotient_local_artinian316 [IsNoetherianRing P]
    (I : Ideal P) (hI : I ≤ maximalIdeal P) (N : ℕ) (hN : 0 < N) :
    IsLocalRing (P ⧸ obstructionThickIdeal316 (maximalIdeal P) I N) ∧
      IsArtinianRing (P ⧸ obstructionThickIdeal316 (maximalIdeal P) I N) :=
  ⟨obstructionQuotient_local316 _ (obstructionThickIdeal_le_maximal316 I hI N hN),
    obstructionQuotient_artinian316 _ (obstructionThickIdeal_le_maximal316 I hI N hN)
      N le_sup_right⟩

theorem obstructionThinQuotient_local_artinian316 [IsNoetherianRing P]
    (I : Ideal P) (hI : I ≤ maximalIdeal P) (N : ℕ) (hN : 0 < N) :
    IsLocalRing (P ⧸ obstructionThinIdeal316 (maximalIdeal P) I N) ∧
      IsArtinianRing (P ⧸ obstructionThinIdeal316 (maximalIdeal P) I N) :=
  ⟨obstructionQuotient_local316 _ (obstructionThinIdeal_le_maximal316 I hI N hN),
    obstructionQuotient_artinian316 _ (obstructionThinIdeal_le_maximal316 I hI N hN)
      N le_sup_right⟩

end PfaffianDescent
