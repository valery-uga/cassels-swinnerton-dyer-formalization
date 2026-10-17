import PfaffianDescent.NativeArtinianObstructionLocal316
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! The concrete obstruction tests reduce to the same presentation residue
field, through canonical surjections with commuting quotient maps. -/
namespace PfaffianDescent
open IsLocalRing

variable {P : Type*} [CommRing P] [IsLocalRing P]

def obstructionQuotientResidueMap316 (J : Ideal P) (hJ : J ≤ maximalIdeal P) :
    P ⧸ J →+* ResidueField P := Ideal.Quotient.factor hJ

theorem obstructionQuotientResidueMap_surjective316
    (J : Ideal P) (hJ : J ≤ maximalIdeal P) :
    Function.Surjective (obstructionQuotientResidueMap316 J hJ) :=
  Ideal.Quotient.factor_surjective hJ

theorem obstructionQuotientResidueMap_mk316 (J : Ideal P)
    (hJ : J ≤ maximalIdeal P) (x : P) :
    obstructionQuotientResidueMap316 J hJ (Ideal.Quotient.mk J x) = residue P x := rfl

theorem obstructionTest_residue_reduction316 (I : Ideal P)
    (hI : I ≤ maximalIdeal P) (N : ℕ) (hN : 0 < N) :
    (obstructionQuotientResidueMap316 _ (obstructionThinIdeal_le_maximal316 I hI N hN)).comp
      (obstructionQuotientReduction316 (maximalIdeal P) I N) =
        obstructionQuotientResidueMap316 _ (obstructionThickIdeal_le_maximal316 I hI N hN) := by
  apply Ideal.Quotient.ringHom_ext
  rfl

theorem obstructionTest_residue_original_quotient316 (I : Ideal P)
    (hI : I ≤ maximalIdeal P) (N : ℕ) (hN : 0 < N) :
    (obstructionQuotientResidueMap316 _ (obstructionThinIdeal_le_maximal316 I hI N hN)).comp
      (Ideal.Quotient.factor
        (show I ≤ obstructionThinIdeal316 (maximalIdeal P) I N from le_sup_left)) =
        obstructionQuotientResidueMap316 I hI := by
  apply Ideal.Quotient.ringHom_ext
  rfl

end PfaffianDescent
