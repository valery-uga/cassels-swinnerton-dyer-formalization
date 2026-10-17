import PfaffianDescent.VoisinLaurentCechExact
import PfaffianDescent.VoisinP3SerreDualExponents

/-!
# The projective-space residue kills Cech boundaries

Full-negative-support Laurent monomials cannot occur on a triple
intersection of the four standard affine charts.  Consequently their
coefficient in every degree-two Cech boundary is zero.  This is the first
descent property needed to turn the explicit Laurent residue coefficient
into a functional on `H³(P³,O(-6))`.
-/

noncomputable section

open scoped AddMonoidAlgebra

namespace PfaffianDescent
namespace LaurentCechExact

open LaurentLocalization LaurentCechCore

universe u

variable (K : Type u) [Field K]

/-- A Laurent exponent with all four coordinates negative cannot occur in a
degree-two Cech cochain satisfying the localization support condition. -/
lemma degreeTwoCech_coefficient_eq_zero_of_fullNegativeSupport
    (z : (Fin 3 → Fin 4) → LaurentPolynomial K)
    (hz : ∀ f (a : LaurentExponent), a ∈ (z f).coeff.support →
      negativeSupport a ⊆ Set.range f)
    (a : LaurentExponent) (ha : negativeSupport a = Set.univ)
    (f : Fin 3 → Fin 4) :
    (z f).coeff a = 0 := by
  rw [← Finsupp.notMem_support_iff]
  intro haf
  have hsub := hz f a haf
  rw [ha, range_fin_three] at hsub
  exact (not_univ_subset_triple (f 0) (f 1) (f 2)) hsub

/-- Every full-negative-support Laurent coefficient vanishes on the image
of the degree-two Cech differential. -/
lemma coefficient_tupleD2_eq_zero_of_fullNegativeSupport
    (z : (Fin 3 → Fin 4) → LaurentPolynomial K)
    (hz : ∀ f (a : LaurentExponent), a ∈ (z f).coeff.support →
      negativeSupport a ⊆ Set.range f)
    (a : LaurentExponent) (ha : negativeSupport a = Set.univ)
    (f : Fin 4 → Fin 4) :
    (tupleD2 z f).coeff a = 0 := by
  rw [coefficient_tupleD2]
  unfold tupleD2
  dsimp only
  rw [degreeTwoCech_coefficient_eq_zero_of_fullNegativeSupport K z hz a ha,
    degreeTwoCech_coefficient_eq_zero_of_fullNegativeSupport K z hz a ha,
    degreeTwoCech_coefficient_eq_zero_of_fullNegativeSupport K z hz a ha,
    degreeTwoCech_coefficient_eq_zero_of_fullNegativeSupport K z hz a ha]
  simp

/-- In particular, every Laurent monomial indexed by a degree-two
polynomial exponent defines a coefficient functional which kills all
degree-two Cech boundaries. -/
lemma p3SerreDualExponent_coefficient_tupleD2_eq_zero
    (z : (Fin 3 → Fin 4) → LaurentPolynomial K)
    (hz : ∀ f (a : LaurentExponent), a ∈ (z f).coeff.support →
      negativeSupport a ⊆ Set.range f)
    (b : Fin 4 →₀ ℕ) (f : Fin 4 → Fin 4) :
    (tupleD2 z f).coeff (p3SerreDualExponent b) = 0 := by
  exact coefficient_tupleD2_eq_zero_of_fullNegativeSupport K z hz
    (p3SerreDualExponent b) (p3SerreDualExponent_negativeSupport b) f

end LaurentCechExact
end PfaffianDescent
