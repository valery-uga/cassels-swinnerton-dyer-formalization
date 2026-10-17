import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.FinCases

/-! SOURCE ONLY / UNVERIFIED164. Convert the ACTUAL two non-zero-divisor
conditions into native IsRegular, retaining the ENTIRE maximal ideal. -/
noncomputable section
namespace PfaffianDescent
open RingTheory.Sequence
open scoped nonZeroDivisors
universe u

/-- A regular pair generating the maximal ideal is a genuine native
regular sequence. This generic adapter assumes the pair conditions only;
the original smooth-cubic caller constructs them internally. -/
theorem regularPair_span_maximalIdeal_isRegular164
    {R : Type u} [CommRing R] [IsLocalRing R] (f g : R)
    (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hspan : Ideal.span ({f, g} : Set R) = IsLocalRing.maximalIdeal R) :
    RingTheory.Sequence.IsRegular R [f, g] := by
  refine ⟨?_, ?_⟩
  · rw [isWeaklyRegular_iff_Fin]
    intro i
    fin_cases i
    · rw [isSMulRegular_quotient_iff_mem_of_smul_mem]
      intro x hx
      have hz : f * x = 0 := by simpa [Ideal.ofList_nil] using hx
      have hx0 : x = 0 := (mem_nonZeroDivisors_iff_left.mp hf) x hz
      simpa [Ideal.ofList_nil] using hx0
    · simp only [List.take, List.length_cons, List.length_nil, Nat.zero_add]
      have hspanOne : Ideal.ofList [f] • (⊤ : Submodule R R) = Ideal.span {f} := by
        rw [Ideal.ofList_singleton]
        simpa using (Ideal.smul_top_eq_map (S := R) (Ideal.span ({f} : Set R)))
      let e := Submodule.quotEquivOfEq _ _ hspanOne
      apply (e.isSMulRegular_congr g).mpr
      apply (isSMulRegular_quotient_iff_mem_of_smul_mem (Ideal.span {f}) g).mpr
      intro x hx
      change g * x ∈ Ideal.span {f} at hx
      have hz : Ideal.Quotient.mk (Ideal.span {f}) g *
          Ideal.Quotient.mk (Ideal.span {f}) x = 0 := by
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
        exact hx
      have hx0 : Ideal.Quotient.mk (Ideal.span {f}) x = 0 :=
        (mem_nonZeroDivisors_iff_left.mp hg) _ hz
      exact Ideal.Quotient.eq_zero_iff_mem.mp hx0
  · intro htop
    have hfg : Ideal.ofList [f, g] = Ideal.span ({f, g} : Set R) := by
      rw [Ideal.ofList_cons, Ideal.ofList_singleton, Ideal.span_insert]
    rw [hfg, hspan, smul_eq_mul, Ideal.mul_top] at htop
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top htop.symm

end PfaffianDescent
