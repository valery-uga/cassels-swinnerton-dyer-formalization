import PfaffianDescent.VoisinLaurentLocalization
import Mathlib.Data.Finsupp.Weight

/-!
# Exponents for the explicit Serre pairing on projective three-space

A degree-two monomial with exponent vector `b` pairs with the Laurent
monomial whose exponents are `-b_i-1`.  The latter has total degree `-6`
and full negative support, exactly the monomials surviving in the top Cech
cohomology of `O_P³(-6)`.
-/

noncomputable section

open MvPolynomial

namespace PfaffianDescent.LaurentLocalization

/-- The exponent vector of the Laurent monomial Serre-dual to a polynomial
monomial. -/
def p3SerreDualExponent (b : Fin 4 →₀ ℕ) : LaurentExponent :=
  -(exponentToInt b) - cechExponent 3 id

lemma cechExponent_three_id_apply (i : Fin 4) :
    cechExponent 3 id i = 1 := by
  classical
  have h : Finset.univ.filter (fun a : Fin 4 => id a = i) = {i} := by
    ext a
    simp
  rw [cechExponent_apply, h]
  simp

@[simp]
lemma p3SerreDualExponent_apply (b : Fin 4 →₀ ℕ) (i : Fin 4) :
    p3SerreDualExponent b i = -(b i : ℤ) - 1 := by
  simp [p3SerreDualExponent, exponentToInt_apply,
    cechExponent_three_id_apply]

lemma p3SerreDualExponent_negative (b : Fin 4 →₀ ℕ) (i : Fin 4) :
    p3SerreDualExponent b i < 0 := by
  rw [p3SerreDualExponent_apply]
  omega

@[simp]
lemma p3SerreDualExponent_negativeSupport (b : Fin 4 →₀ ℕ) :
    negativeSupport (p3SerreDualExponent b) = Set.univ := by
  ext i
  simp only [negativeSupport, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact p3SerreDualExponent_negative b i

lemma p3SerreDualExponent_totalDegree (b : Fin 4 →₀ ℕ) :
    totalDegree (p3SerreDualExponent b) = -(b.degree : ℤ) - 4 := by
  have hc : totalDegree (cechExponent 3 id) = 4 := by
    rw [show totalDegree (cechExponent 3 id) =
      ∑ i, cechExponent 3 id i by rfl]
    simp [cechExponent_three_id_apply]
  rw [p3SerreDualExponent, sub_eq_add_neg, totalDegree_add,
    totalDegree_neg, totalDegree_neg, totalDegree_exponentToInt,
    hc, Finsupp.degree_eq_sum]
  ring

lemma p3SerreDualExponent_totalDegree_of_degree_two
    (b : Fin 4 →₀ ℕ) (hb : b.degree = 2) :
    totalDegree (p3SerreDualExponent b) = -6 := by
  rw [p3SerreDualExponent_totalDegree, hb]
  norm_num

lemma p3SerreDualExponent_injective :
    Function.Injective p3SerreDualExponent := by
  intro b c h
  apply Finsupp.ext
  intro i
  have hi := congrArg (fun a : LaurentExponent ↦ a i) h
  simp only [p3SerreDualExponent_apply] at hi
  omega

/-- Recover the polynomial exponent by sending a strictly negative Laurent
exponent `a_i` to the natural number `-a_i-1`. -/
def p3SerrePolynomialExponent (a : LaurentExponent) : Fin 4 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => Int.toNat (-a i - 1))

@[simp]
lemma p3SerrePolynomialExponent_apply (a : LaurentExponent) (i : Fin 4) :
    p3SerrePolynomialExponent a i = Int.toNat (-a i - 1) := by
  let f : Fin 4 → ℕ := fun j => Int.toNat (-a j - 1)
  have h := congrFun (Finsupp.equivFunOnFinite.apply_symm_apply f) i
  simpa only [p3SerrePolynomialExponent, f,
    Finsupp.equivFunOnFinite_apply] using h

lemma p3SerreDualExponent_polynomialExponent_of_negative
    (a : LaurentExponent) (ha : ∀ i, a i < 0) :
    p3SerreDualExponent (p3SerrePolynomialExponent a) = a := by
  apply Finsupp.ext
  intro i
  have hai := ha i
  rw [p3SerreDualExponent_apply, p3SerrePolynomialExponent_apply,
    Int.toNat_of_nonneg (by omega : 0 ≤ -a i - 1)]
  omega

lemma p3SerreDualExponent_polynomialExponent_of_negativeSupport
    (a : LaurentExponent) (ha : negativeSupport a = Set.univ) :
    p3SerreDualExponent (p3SerrePolynomialExponent a) = a := by
  apply p3SerreDualExponent_polynomialExponent_of_negative
  intro i
  have hi : i ∈ negativeSupport a := by rw [ha]; exact Set.mem_univ i
  change a i < 0 at hi
  exact hi

lemma p3SerrePolynomialExponent_degree_of_totalDegree_of_negative
    (a : LaurentExponent) (hdegree : totalDegree a = -6)
    (ha : ∀ i, a i < 0) :
    (p3SerrePolynomialExponent a).degree = 2 := by
  have hrecover := p3SerreDualExponent_polynomialExponent_of_negative a ha
  have htotal := congrArg totalDegree hrecover
  rw [p3SerreDualExponent_totalDegree, hdegree] at htotal
  omega

lemma p3SerrePolynomialExponent_degree_of_totalDegree_of_negativeSupport
    (a : LaurentExponent) (hdegree : totalDegree a = -6)
    (ha : negativeSupport a = Set.univ) :
    (p3SerrePolynomialExponent a).degree = 2 := by
  apply p3SerrePolynomialExponent_degree_of_totalDegree_of_negative a hdegree
  intro i
  have hi : i ∈ negativeSupport a := by rw [ha]; exact Set.mem_univ i
  exact hi

/-- Degree-two polynomial monomials are in bijection with the full-negative-
support Laurent monomials of total degree `-6`.  This is the basis-level
content of the projective-three-space Serre pairing used for the cubic
surface. -/
def p3SerreDualExponentEquiv :
    {b : Fin 4 →₀ ℕ // b.degree = 2} ≃
      {a : LaurentExponent //
        totalDegree a = -6 ∧ negativeSupport a = Set.univ} where
  toFun b := ⟨p3SerreDualExponent b,
    p3SerreDualExponent_totalDegree_of_degree_two b b.property,
    p3SerreDualExponent_negativeSupport b⟩
  invFun a := ⟨p3SerrePolynomialExponent a,
    p3SerrePolynomialExponent_degree_of_totalDegree_of_negativeSupport
      a a.property.1 a.property.2⟩
  left_inv b := by
    apply Subtype.ext
    apply p3SerreDualExponent_injective
    apply p3SerreDualExponent_polynomialExponent_of_negative
    exact p3SerreDualExponent_negative b
  right_inv a := by
    apply Subtype.ext
    exact p3SerreDualExponent_polynomialExponent_of_negativeSupport
      a a.property.2

end PfaffianDescent.LaurentLocalization
