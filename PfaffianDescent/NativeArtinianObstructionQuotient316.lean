import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! The physical square-zero quotient used to detect a cotangent obstruction.
The algebraic identities here hold over any commutative ring. Locality,
Artinianity, and detection of a nonzero relation are separate obligations. -/
namespace PfaffianDescent

variable {P : Type*} [CommRing P] (m I : Ideal P) (N : ℕ)

def obstructionThickIdeal316 : Ideal P := m * I ⊔ m ^ N

def obstructionThinIdeal316 : Ideal P := I ⊔ m ^ N

theorem obstructionThickIdeal_le_thin316 :
    obstructionThickIdeal316 m I N ≤ obstructionThinIdeal316 m I N :=
  sup_le_sup Ideal.mul_le_right le_rfl

def obstructionQuotientReduction316 :
    P ⧸ obstructionThickIdeal316 m I N →+* P ⧸ obstructionThinIdeal316 m I N :=
  Ideal.Quotient.factor (obstructionThickIdeal_le_thin316 m I N)

theorem obstructionQuotientReduction_surjective316 :
    Function.Surjective (obstructionQuotientReduction316 m I N) :=
  Ideal.Quotient.factor_surjective _

theorem obstructionQuotientReduction_mk316 (x : P) :
    obstructionQuotientReduction316 m I N
      (Ideal.Quotient.mk (obstructionThickIdeal316 m I N) x) =
        Ideal.Quotient.mk (obstructionThinIdeal316 m I N) x := rfl

theorem obstructionQuotientReduction_kernel316 :
    RingHom.ker (obstructionQuotientReduction316 m I N) =
      I.map (Ideal.Quotient.mk (obstructionThickIdeal316 m I N)) := by
  rw [obstructionQuotientReduction316, Ideal.Quotient.factor_ker]
  have hpow : (m ^ N).map (Ideal.Quotient.mk (obstructionThickIdeal316 m I N)) = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker _).2
    rw [Ideal.mk_ker]
    exact le_sup_right
  rw [obstructionThinIdeal316, Ideal.map_sup, hpow, sup_bot_eq]

theorem obstructionQuotientReduction_kernel_sq_zero316 (hI : I ≤ m) :
    RingHom.ker (obstructionQuotientReduction316 m I N) ^ 2 = ⊥ := by
  rw [obstructionQuotientReduction_kernel316, ← Ideal.map_pow]
  apply (Ideal.map_eq_bot_iff_le_ker _).2
  rw [Ideal.mk_ker, pow_two]
  exact (Ideal.mul_mono hI le_rfl).trans le_sup_left

theorem obstructionQuotientReduction_kernel_annihilated316 :
    m.map (Ideal.Quotient.mk (obstructionThickIdeal316 m I N)) *
      RingHom.ker (obstructionQuotientReduction316 m I N) = ⊥ := by
  rw [obstructionQuotientReduction_kernel316, ← Ideal.map_mul]
  apply (Ideal.map_eq_bot_iff_le_ker _).2
  rw [Ideal.mk_ker]
  exact le_sup_left

theorem obstructionQuotient_maximal_power_zero316 :
    m.map (Ideal.Quotient.mk (obstructionThickIdeal316 m I N)) ^ N = ⊥ := by
  rw [← Ideal.map_pow]
  apply (Ideal.map_eq_bot_iff_le_ker _).2
  rw [Ideal.mk_ker]
  exact le_sup_right

theorem obstructionQuotient_relation_nonzero316 {x : P}
    (hx : x ∉ obstructionThickIdeal316 m I N) :
    Ideal.Quotient.mk (obstructionThickIdeal316 m I N) x ≠ 0 :=
  fun h => hx ((Ideal.Quotient.eq_zero_iff_mem).1 h)

end PfaffianDescent
