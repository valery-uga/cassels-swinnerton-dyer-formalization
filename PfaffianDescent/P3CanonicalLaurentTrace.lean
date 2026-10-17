import PfaffianDescent.VoisinP3TopCechExact

/-! # Scalar canonical Laurent residue in degree minus four -/
noncomputable section
open scoped AddMonoidAlgebra BigOperators
namespace PfaffianDescent.LaurentCechExact
open LaurentLocalization LaurentCechCore
universe u
variable (K : Type u) [Field K]

theorem laurent_tuple_exact_three_of_full_support_coefficients_zero
    (d : ℤ)
    (w : (Fin 4 → Fin 4) → LaurentPolynomial K)
    (hw : ∀ f (a : LaurentExponent), a ∈ (w f).coeff.support →
      totalDegree a = d ∧ negativeSupport a ⊆ Set.range f)
    (hdw : ∀ f, tupleD3 w f = 0)
    (hres : ∀ a : LaurentExponent, totalDegree a = d →
      negativeSupport a = Set.univ → (w id).coeff a = 0) :
    ∃ z : (Fin 3 → Fin 4) → LaurentPolynomial K,
      (∀ f (a : LaurentExponent), a ∈ (z f).coeff.support →
        totalDegree a = d ∧ negativeSupport a ⊆ Set.range f) ∧
      ∀ f, tupleD2 z f = w f := by
  classical
  let S := cochainSupport K w
  have hexact (a : LaurentExponent) :
      ∃ za : (Fin 3 → Fin 4) → K,
        TupleSupported (negativeSupport a) za ∧
        ∀ f, tupleD2 za f = (w f).coeff a := by
    have hsupp := coefficient_tupleSupported K w hw a
    have hcocycle : ∀ f, tupleD3 (fun g => (w g).coeff a) f = 0 := by
      intro f
      rw [← coefficient_tupleD3]
      rw [hdw f]
      rfl
    by_cases hfull : negativeSupport a = Set.univ
    · have hsuppUniv :
          TupleSupported Set.univ (fun g => (w g).coeff a) := by
        simpa [hfull] using hsupp
      have hid : (w id).coeff a = 0 := by
        by_cases haS : a ∈ S
        · have hdegree : totalDegree a = d :=
            cochainSupport_degree K d w hw haS
          exact hres a hdegree hfull
        · rw [← Finsupp.notMem_support_iff]
          intro ha
          exact haS ((mem_cochainSupport_iff K w a).2 ⟨id, ha⟩)
      have hzero : (fun g => (w g).coeff a) = 0 :=
        tupleSupported_univ_cocycle_eq_zero_of_id_eq_zero
          (fun g => (w g).coeff a) hsuppUniv hcocycle hid
      refine ⟨0, ?_, ?_⟩
      · intro f _hf
        rfl
      · intro f
        have hf := congrFun hzero f
        simpa [tupleD2] using hf.symm
    · exact tuple_exact_three_of_ne_univ
        (negativeSupport a) hfull (fun g => (w g).coeff a) hsupp hcocycle
  let za : LaurentExponent → (Fin 3 → Fin 4) → K :=
    fun a => Classical.choose (hexact a)
  have hza_support (a : LaurentExponent) :
      TupleSupported (negativeSupport a) (za a) :=
    (Classical.choose_spec (hexact a)).1
  have hza_diff (a : LaurentExponent) :
      ∀ f, tupleD2 (za a) f = (w f).coeff a :=
    (Classical.choose_spec (hexact a)).2
  let z : (Fin 3 → Fin 4) → LaurentPolynomial K := fun f =>
    ∑ a ∈ S, AddMonoidAlgebra.single a (za a f)
  refine ⟨z, ?_, ?_⟩
  · intro f a ha
    have hcoeff : (z f).coeff a ≠ 0 := Finsupp.mem_support_iff.mp ha
    have hcoeffFormula : (z f).coeff a = if a ∈ S then za a f else 0 := by
      simpa [z] using coeff_sum_single K S (fun b => za b f) a
    have haS : a ∈ S := by
      by_contra haS
      apply hcoeff
      rw [hcoeffFormula, if_neg haS]
    refine ⟨cochainSupport_degree K d w hw haS, ?_⟩
    by_contra hnegative
    have hzero := hza_support a f hnegative
    apply hcoeff
    rw [hcoeffFormula, if_pos haS, hzero]
  · intro f
    ext a
    rw [coefficient_tupleD2]
    have hzcoeff (g : Fin 3 → Fin 4) :
        (z g).coeff a = if a ∈ S then za a g else 0 := by
      simpa [z] using coeff_sum_single K S (fun b => za b g) a
    rw [tupleD2, hzcoeff, hzcoeff, hzcoeff, hzcoeff]
    by_cases haS : a ∈ S
    · simp only [if_pos haS]
      exact hza_diff a f
    · have haw : (w f).coeff a = 0 := by
        rw [← Finsupp.notMem_support_iff]
        intro haf
        exact haS ((mem_cochainSupport_iff K w a).2 ⟨f, haf⟩)
      simp [haS, haw]

/-- The only full-negative-support exponent of canonical degree minus four
has every coordinate minus one. -/
theorem p3CanonicalExponent_unique (a : LaurentExponent)
    (hdegree : totalDegree a = -4) (hfull : negativeSupport a = Set.univ) :
    a = p3SerreDualExponent 0 := by
  have hr := p3SerreDualExponent_polynomialExponent_of_negativeSupport a hfull
  have ht := congrArg totalDegree hr
  rw [p3SerreDualExponent_totalDegree, hdegree] at ht
  have hb : (p3SerrePolynomialExponent a).degree = 0 := by omega
  have hz : p3SerrePolynomialExponent a = 0 := (Finsupp.degree_eq_zero_iff _).mp hb
  rw [hz] at hr
  exact hr.symm

/-- Vanishing of the single canonical residue forces an actual Laurent
canonical-degree top cocycle to be an actual boundary. -/
theorem laurent_tuple_exact_three_of_degree_neg_four_of_trace_zero
    (w : (Fin 4 → Fin 4) → LaurentPolynomial K)
    (hw : ∀ f (a : LaurentExponent), a ∈ (w f).coeff.support →
      totalDegree a = -4 ∧ negativeSupport a ⊆ Set.range f)
    (hdw : ∀ f, tupleD3 w f = 0)
    (htrace : (w id).coeff (p3SerreDualExponent 0) = 0) :
    ∃ z : (Fin 3 → Fin 4) → LaurentPolynomial K,
      (∀ f (a : LaurentExponent), a ∈ (z f).coeff.support →
        totalDegree a = -4 ∧ negativeSupport a ⊆ Set.range f) ∧
      ∀ f, tupleD2 z f = w f := by
  apply laurent_tuple_exact_three_of_full_support_coefficients_zero K (-4) w hw hdw
  intro a ha hf
  rw [p3CanonicalExponent_unique a ha hf]
  exact htrace

end PfaffianDescent.LaurentCechExact
