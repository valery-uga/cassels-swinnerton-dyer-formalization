import PfaffianDescent.VoisinLaurentLocalization
import PfaffianDescent.VoisinLaurentCechCore

noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped AddMonoidAlgebra BigOperators
universe u
namespace PfaffianDescent.LaurentCechExact

open LaurentLocalization LaurentCechCore

variable (K : Type u) [Field K]

abbrev LaurentExponent := LaurentLocalization.LaurentExponent
abbrev LaurentPolynomial := LaurentLocalization.LaurentPolynomial K

def cochainSupport {q : ℕ}
    (c : (Fin (q + 1) → Fin 4) → LaurentPolynomial K) : Finset LaurentExponent :=
  Finset.univ.biUnion fun f => (c f).coeff.support

lemma mem_cochainSupport_iff {q : ℕ}
    (c : (Fin (q + 1) → Fin 4) → LaurentPolynomial K) (a : LaurentExponent) :
    a ∈ cochainSupport K c ↔ ∃ f, a ∈ (c f).coeff.support := by
  classical
  simp [cochainSupport]

lemma coeff_sum_single (s : Finset LaurentExponent)
    (c : LaurentExponent → K) (b : LaurentExponent) :
    (∑ a ∈ s, AddMonoidAlgebra.single a (c a)).coeff b =
      if b ∈ s then c b else 0 := by
  classical
  rw [AddMonoidAlgebra.coeff_sum]
  simp_rw [AddMonoidAlgebra.coeff_single]
  rw [Finsupp.finsetSum_apply]
  simp_rw [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

lemma cochainSupport_degree
    {q : ℕ} (d : ℤ) (c : (Fin (q + 1) → Fin 4) → LaurentPolynomial K)
    (hc : ∀ f (a : LaurentExponent), a ∈ (c f).coeff.support →
      totalDegree a = d ∧ negativeSupport a ⊆ Set.range f)
    {a : LaurentExponent} (ha : a ∈ cochainSupport K c) :
    totalDegree a = d := by
  obtain ⟨f, haf⟩ := (mem_cochainSupport_iff K c a).mp ha
  exact (hc f a haf).1

lemma coefficient_tupleSupported
    {q : ℕ} (c : (Fin (q + 1) → Fin 4) → LaurentPolynomial K)
    {d : ℤ}
    (hc : ∀ f (a : LaurentExponent), a ∈ (c f).coeff.support →
      totalDegree a = d ∧ negativeSupport a ⊆ Set.range f)
    (a : LaurentExponent) :
    TupleSupported (negativeSupport a) (fun f => (c f).coeff a) := by
  intro f hnot
  rw [← Finsupp.notMem_support_iff]
  intro ha
  exact hnot (hc f a ha).2

lemma coefficient_tupleD1
    (y : (Fin 2 → Fin 4) → LaurentPolynomial K) (a : LaurentExponent)
    (f : Fin 3 → Fin 4) :
    (tupleD1 y f).coeff a =
      tupleD1 (fun g => (y g).coeff a) f := by
  rfl

lemma coefficient_tupleD0
    (x : (Fin 1 → Fin 4) → LaurentPolynomial K) (a : LaurentExponent)
    (f : Fin 2 → Fin 4) :
    (tupleD0 x f).coeff a =
      tupleD0 (fun g => (x g).coeff a) f := by
  rfl

lemma laurent_tuple_exact_one_of_degree
    (d : ℤ)
    (y : (Fin 2 → Fin 4) → LaurentPolynomial K)
    (hy : ∀ f (a : LaurentExponent), a ∈ (y f).coeff.support →
      totalDegree a = d ∧ negativeSupport a ⊆ Set.range f)
    (hdy : ∀ f, tupleD1 y f = 0) :
    ∃ x : (Fin 1 → Fin 4) → LaurentPolynomial K,
      (∀ f (a : LaurentExponent), a ∈ (x f).coeff.support →
        totalDegree a = d ∧ negativeSupport a ⊆ Set.range f) ∧
      ∀ f, tupleD0 x f = y f := by
  classical
  let S := cochainSupport K y
  have hexact (a : LaurentExponent) :
      ∃ xa : (Fin 1 → Fin 4) → K,
        TupleSupported (negativeSupport a) xa ∧
        ∀ f, tupleD0 xa f = (y f).coeff a := by
    have hsupp := coefficient_tupleSupported K y hy a
    have hcocycle : ∀ f, tupleD1 (fun g => (y g).coeff a) f = 0 := by
      intro f
      rw [← coefficient_tupleD1]
      rw [hdy f]
      rfl
    obtain ⟨xa, hxa, hdxa⟩ :=
      tuple_exact_one (negativeSupport a) (fun g => (y g).coeff a) hsupp hcocycle
    exact ⟨xa, hxa, hdxa⟩
  let xa : LaurentExponent → (Fin 1 → Fin 4) → K :=
    fun a => Classical.choose (hexact a)
  have hxa_support (a : LaurentExponent) :
      TupleSupported (negativeSupport a) (xa a) :=
    (Classical.choose_spec (hexact a)).1
  have hxa_diff (a : LaurentExponent) :
      ∀ f, tupleD0 (xa a) f = (y f).coeff a :=
    (Classical.choose_spec (hexact a)).2
  let x : (Fin 1 → Fin 4) → LaurentPolynomial K := fun f =>
    ∑ a ∈ S, AddMonoidAlgebra.single a (xa a f)
  refine ⟨x, ?_, ?_⟩
  · intro f a ha
    have hcoeff : (x f).coeff a ≠ 0 := Finsupp.mem_support_iff.mp ha
    have hcoeffFormula : (x f).coeff a = if a ∈ S then xa a f else 0 := by
      simpa [x] using coeff_sum_single K S (fun b => xa b f) a
    have haS : a ∈ S := by
      by_contra haS
      apply hcoeff
      rw [hcoeffFormula, if_neg haS]
    refine ⟨cochainSupport_degree K d y hy haS, ?_⟩
    by_contra hnegative
    have hzero := hxa_support a f hnegative
    apply hcoeff
    rw [hcoeffFormula, if_pos haS, hzero]
  · intro f
    ext a
    rw [coefficient_tupleD0]
    have hxcoeff (g : Fin 1 → Fin 4) :
        (x g).coeff a = if a ∈ S then xa a g else 0 := by
      simpa [x] using coeff_sum_single K S (fun b => xa b g) a
    rw [tupleD0, hxcoeff, hxcoeff]
    by_cases haS : a ∈ S
    · simp only [if_pos haS]
      exact hxa_diff a f
    · have hay : (y f).coeff a = 0 := by
        rw [← Finsupp.notMem_support_iff]
        intro haf
        exact haS ((mem_cochainSupport_iff K y a).2 ⟨f, haf⟩)
      simp [haS, hay]

lemma coefficient_tupleD2
    (z : (Fin 3 → Fin 4) → LaurentPolynomial K) (a : LaurentExponent)
    (f : Fin 4 → Fin 4) :
    (tupleD2 z f).coeff a =
      tupleD2 (fun g => (z g).coeff a) f := by
  rfl

lemma laurent_tuple_exact_two_of_degree
    (d : ℤ)
    (z : (Fin 3 → Fin 4) → LaurentPolynomial K)
    (hz : ∀ f (a : LaurentExponent), a ∈ (z f).coeff.support →
      totalDegree a = d ∧ negativeSupport a ⊆ Set.range f)
    (hdz : ∀ f, tupleD2 z f = 0) :
    ∃ y : (Fin 2 → Fin 4) → LaurentPolynomial K,
      (∀ f (a : LaurentExponent), a ∈ (y f).coeff.support →
        totalDegree a = d ∧ negativeSupport a ⊆ Set.range f) ∧
      ∀ f, tupleD1 y f = z f := by
  classical
  let S := cochainSupport K z
  have hexact (a : LaurentExponent) :
      ∃ ya : (Fin 2 → Fin 4) → K,
        TupleSupported (negativeSupport a) ya ∧
        ∀ f, tupleD1 ya f = (z f).coeff a := by
    have hsupp := coefficient_tupleSupported K z hz a
    have hcocycle : ∀ f, tupleD2 (fun g => (z g).coeff a) f = 0 := by
      intro f
      rw [← coefficient_tupleD2]
      rw [hdz f]
      rfl
    obtain ⟨ya, hya, hdya⟩ :=
      tuple_exact_two (negativeSupport a) (fun g => (z g).coeff a) hsupp hcocycle
    exact ⟨ya, hya, hdya⟩
  let ya : LaurentExponent → (Fin 2 → Fin 4) → K :=
    fun a => Classical.choose (hexact a)
  have hya_support (a : LaurentExponent) :
      TupleSupported (negativeSupport a) (ya a) :=
    (Classical.choose_spec (hexact a)).1
  have hya_diff (a : LaurentExponent) :
      ∀ f, tupleD1 (ya a) f = (z f).coeff a :=
    (Classical.choose_spec (hexact a)).2
  let y : (Fin 2 → Fin 4) → LaurentPolynomial K := fun f =>
    ∑ a ∈ S, AddMonoidAlgebra.single a (ya a f)
  refine ⟨y, ?_, ?_⟩
  · intro f a ha
    have hcoeff : (y f).coeff a ≠ 0 := Finsupp.mem_support_iff.mp ha
    have hcoeffFormula : (y f).coeff a = if a ∈ S then ya a f else 0 := by
      simpa [y] using coeff_sum_single K S (fun b => ya b f) a
    have haS : a ∈ S := by
      by_contra haS
      apply hcoeff
      rw [hcoeffFormula, if_neg haS]
    refine ⟨cochainSupport_degree K d z hz haS, ?_⟩
    by_contra hnegative
    have hzero := hya_support a f hnegative
    apply hcoeff
    rw [hcoeffFormula, if_pos haS, hzero]
  · intro f
    ext a
    rw [coefficient_tupleD1]
    have hycoeff (g : Fin 2 → Fin 4) :
        (y g).coeff a = if a ∈ S then ya a g else 0 := by
      simpa [y] using coeff_sum_single K S (fun b => ya b g) a
    rw [tupleD1, hycoeff, hycoeff, hycoeff]
    by_cases haS : a ∈ S
    · simp only [if_pos haS]
      exact hya_diff a f
    · have haz : (z f).coeff a = 0 := by
        rw [← Finsupp.notMem_support_iff]
        intro haf
        exact haS ((mem_cochainSupport_iff K z a).2 ⟨f, haf⟩)
      simp [haS, haz]

/-- Degree-one exactness specialized to total Laurent degree zero. -/
lemma laurent_tuple_exact_one
    (y : (Fin 2 → Fin 4) → LaurentPolynomial K)
    (hy : ∀ f (a : LaurentExponent), a ∈ (y f).coeff.support →
      totalDegree a = 0 ∧ negativeSupport a ⊆ Set.range f)
    (hdy : ∀ f, tupleD1 y f = 0) :
    ∃ x : (Fin 1 → Fin 4) → LaurentPolynomial K,
      (∀ f (a : LaurentExponent), a ∈ (x f).coeff.support →
        totalDegree a = 0 ∧ negativeSupport a ⊆ Set.range f) ∧
      ∀ f, tupleD0 x f = y f :=
  laurent_tuple_exact_one_of_degree K 0 y hy hdy

/-- Degree-two exactness specialized to total Laurent degree zero. -/
lemma laurent_tuple_exact_two
    (z : (Fin 3 → Fin 4) → LaurentPolynomial K)
    (hz : ∀ f (a : LaurentExponent), a ∈ (z f).coeff.support →
      totalDegree a = 0 ∧ negativeSupport a ⊆ Set.range f)
    (hdz : ∀ f, tupleD2 z f = 0) :
    ∃ y : (Fin 2 → Fin 4) → LaurentPolynomial K,
      (∀ f (a : LaurentExponent), a ∈ (y f).coeff.support →
        totalDegree a = 0 ∧ negativeSupport a ⊆ Set.range f) ∧
      ∀ f, tupleD1 y f = z f :=
  laurent_tuple_exact_two_of_degree K 0 z hz hdz

end PfaffianDescent.LaurentCechExact
