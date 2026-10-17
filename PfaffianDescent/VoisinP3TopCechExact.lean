import PfaffianDescent.VoisinP3TopCechDetection

/-!
# Exactness of top Cech cocycles with zero projective residue

For the standard four-chart cover of projective three-space, a Laurent
degree `-6` degree-three cocycle is a degree-two boundary when all residue
coefficients dual to quadratic monomials vanish.  The proof splits the
finite Laurent support exponent by exponent.  Proper negative support is
contractible, while full negative support is detected by the identity
component and hence by the residue coefficients.
-/

noncomputable section

open scoped AddMonoidAlgebra BigOperators

namespace PfaffianDescent
namespace LaurentCechExact

open LaurentLocalization LaurentCechCore

universe u

variable (K : Type u) [Field K]

lemma coefficient_tupleD3
    (w : (Fin 4 → Fin 4) → LaurentPolynomial K) (a : LaurentExponent)
    (f : Fin 5 → Fin 4) :
    (tupleD3 w f).coeff a =
      tupleD3 (fun g => (w g).coeff a) f := by
  rfl

/-- A top Cech cocycle is a boundary whenever its homogeneous degree admits
no Laurent monomial with all four exponents negative. -/
theorem laurent_tuple_exact_three_of_degree_of_no_full_support
    (d : ℤ)
    (hproper : ∀ a : LaurentExponent,
      totalDegree a = d → negativeSupport a ≠ Set.univ)
    (w : (Fin 4 → Fin 4) → LaurentPolynomial K)
    (hw : ∀ f (a : LaurentExponent), a ∈ (w f).coeff.support →
      totalDegree a = d ∧ negativeSupport a ⊆ Set.range f)
    (hdw : ∀ f, tupleD3 w f = 0) :
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
    by_cases haS : a ∈ S
    · exact tuple_exact_three_of_ne_univ
        (negativeSupport a)
        (hproper a (cochainSupport_degree K d w hw haS))
        (fun g => (w g).coeff a) hsupp hcocycle
    · refine ⟨0, ?_, ?_⟩
      · intro f _hf
        rfl
      · intro f
        have haw : (w f).coeff a = 0 := by
          rw [← Finsupp.notMem_support_iff]
          intro haf
          exact haS ((mem_cochainSupport_iff K w a).2 ⟨f, haf⟩)
        simp [tupleD2, haw]
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

/-- Degree `-3` has no full-negative-support Laurent monomials, so every
degree-three Cech cocycle in that degree is a boundary. -/
theorem laurent_tuple_exact_three_of_degree_neg_three
    (w : (Fin 4 → Fin 4) → LaurentPolynomial K)
    (hw : ∀ f (a : LaurentExponent), a ∈ (w f).coeff.support →
      totalDegree a = -3 ∧ negativeSupport a ⊆ Set.range f)
    (hdw : ∀ f, tupleD3 w f = 0) :
    ∃ z : (Fin 3 → Fin 4) → LaurentPolynomial K,
      (∀ f (a : LaurentExponent), a ∈ (z f).coeff.support →
        totalDegree a = -3 ∧ negativeSupport a ⊆ Set.range f) ∧
      ∀ f, tupleD2 z f = w f := by
  apply laurent_tuple_exact_three_of_degree_of_no_full_support K (-3)
  intro a hdegree hfull
  have hrecover :=
    p3SerreDualExponent_polynomialExponent_of_negativeSupport a hfull
  have htotal := congrArg totalDegree hrecover
  rw [p3SerreDualExponent_totalDegree, hdegree] at htotal
  omega
  exact hw
  exact hdw

/-- A homogeneous degree `-6` top Cech cocycle whose quadratic residue
coefficients all vanish is a degree-two boundary, with the primitive
retaining the expected localization support and homogeneity. -/
theorem laurent_tuple_exact_three_of_degree_neg_six_of_residue_zero
    (w : (Fin 4 → Fin 4) → LaurentPolynomial K)
    (hw : ∀ f (a : LaurentExponent), a ∈ (w f).coeff.support →
      totalDegree a = -6 ∧ negativeSupport a ⊆ Set.range f)
    (hdw : ∀ f, tupleD3 w f = 0)
    (hres : ∀ b : Fin 4 →₀ ℕ, b.degree = 2 →
      p3SerreResidueCoefficient K b w = 0) :
    ∃ z : (Fin 3 → Fin 4) → LaurentPolynomial K,
      (∀ f (a : LaurentExponent), a ∈ (z f).coeff.support →
        totalDegree a = -6 ∧ negativeSupport a ⊆ Set.range f) ∧
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
        · have hdegree : totalDegree a = -6 :=
            cochainSupport_degree K (-6) w hw haS
          let b := p3SerrePolynomialExponent a
          have hb : b.degree = 2 :=
            p3SerrePolynomialExponent_degree_of_totalDegree_of_negativeSupport
              a hdegree hfull
          have hrecover : p3SerreDualExponent b = a :=
            p3SerreDualExponent_polynomialExponent_of_negativeSupport a hfull
          have hzero := hres b hb
          change (w id).coeff (p3SerreDualExponent b) = 0 at hzero
          rwa [hrecover] at hzero
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
    refine ⟨cochainSupport_degree K (-6) w hw haS, ?_⟩
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

end LaurentCechExact
end PfaffianDescent
