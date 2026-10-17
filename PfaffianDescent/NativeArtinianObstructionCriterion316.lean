import PfaffianDescent.NativeArtinianObstructionDetection316
import PfaffianDescent.NativeArtinianObstructionNoLift316

/-! Actual finite Artinian quotient tests detect the kernel of the residue
differential on relations. This is an algebraic criterion, not yet the geometric
classifier's lifting construction or its formal smoothness conclusion. -/
namespace PfaffianDescent
open IsLocalRing KaehlerDifferential

variable {R P : Type*} [CommRing R] [CommRing P] [Algebra R P]
  [IsLocalRing P] [IsNoetherianRing P]

theorem obstruction_exists_artinian_nolift316 (I : Ideal P)
    (hI : I ≤ maximalIdeal P) {x : P} (hx : x ∈ I)
    (hD : D R P x ∈ maximalIdeal P • (⊤ : Submodule P Ω[P⁄R]))
    (hne : x ∉ maximalIdeal P * I) :
    ∃ N : ℕ, 0 < N ∧
      IsLocalRing (P ⧸ obstructionThickIdeal316 (maximalIdeal P) I N) ∧
      IsArtinianRing (P ⧸ obstructionThickIdeal316 (maximalIdeal P) I N) ∧
      IsLocalRing (P ⧸ obstructionThinIdeal316 (maximalIdeal P) I N) ∧
      IsArtinianRing (P ⧸ obstructionThinIdeal316 (maximalIdeal P) I N) ∧
      ¬ ∃ l : P ⧸ I →ₐ[R] P ⧸ obstructionThickIdeal316 (maximalIdeal P) I N,
        (Ideal.Quotient.factorₐ R (obstructionThickIdeal_le_thin316 (maximalIdeal P) I N)).comp l =
          Ideal.Quotient.factorₐ R
            (show I ≤ obstructionThinIdeal316 (maximalIdeal P) I N from le_sup_left) := by
  obtain ⟨N, hN, hxN⟩ := obstruction_exists_positive_power_not_mem316
    (maximalIdeal P * I) Ideal.mul_le_left hne
  obtain ⟨hB, hBA⟩ := obstructionThickQuotient_local_artinian316 I hI N hN
  obtain ⟨hS, hSA⟩ := obstructionThinQuotient_local_artinian316 I hI N hN
  refine ⟨N, hN, hB, hBA, hS, hSA, ?_⟩
  rintro ⟨l, hl⟩
  exact obstructionQuotient_no_lift316 (maximalIdeal P) I hI N hx hD hxN l hl

theorem obstruction_relation_mem_of_quotient_lifts316 (I : Ideal P)
    (hI : I ≤ maximalIdeal P)
    (hlift : ∀ N : ℕ, 0 < N →
      ∃ l : P ⧸ I →ₐ[R] P ⧸ obstructionThickIdeal316 (maximalIdeal P) I N,
        (Ideal.Quotient.factorₐ R (obstructionThickIdeal_le_thin316 (maximalIdeal P) I N)).comp l =
          Ideal.Quotient.factorₐ R
            (show I ≤ obstructionThinIdeal316 (maximalIdeal P) I N from le_sup_left))
    {x : P} (hx : x ∈ I)
    (hD : D R P x ∈ maximalIdeal P • (⊤ : Submodule P Ω[P⁄R])) :
    x ∈ maximalIdeal P * I := by
  by_contra hne
  obtain ⟨N, hN, _, _, _, _, hno⟩ := obstruction_exists_artinian_nolift316 I hI hx hD hne
  exact hno (hlift N hN)

end PfaffianDescent
