import PfaffianDescent.VoisinP3SerreResidueBoundary

/-!
# Residue coefficient functionals for projective-three-space Serre duality

For every degree-two polynomial exponent `b`, evaluation of a degree-three
Cech cochain at the identity four-chart tuple followed by extraction of the
Laurent coefficient `-b_i-1` is an additive functional.  These functionals
kill degree-two Cech boundaries and jointly detect every total-degree `-6`,
full-negative-support Laurent component.
-/

noncomputable section

open scoped AddMonoidAlgebra

namespace PfaffianDescent
namespace LaurentCechExact

open LaurentLocalization LaurentCechCore

universe u

variable (K : Type u) [Field K]

/-- The Laurent residue coefficient dual to the polynomial monomial with
exponent `b`. -/
def p3SerreResidueCoefficient (b : Fin 4 →₀ ℕ) :
    ((Fin 4 → Fin 4) → LaurentPolynomial K) →+ K where
  toFun w := (w id).coeff (p3SerreDualExponent b)
  map_zero' := by simp
  map_add' x y := by simp

@[simp]
lemma p3SerreResidueCoefficient_apply
    (b : Fin 4 →₀ ℕ)
    (w : (Fin 4 → Fin 4) → LaurentPolynomial K) :
    p3SerreResidueCoefficient K b w =
      (w id).coeff (p3SerreDualExponent b) := rfl

/-- Every residue coefficient indexed by a polynomial monomial kills every
degree-two Cech boundary satisfying the localization support condition. -/
lemma p3SerreResidueCoefficient_tupleD2_eq_zero
    (z : (Fin 3 → Fin 4) → LaurentPolynomial K)
    (hz : ∀ f (a : LaurentExponent), a ∈ (z f).coeff.support →
      negativeSupport a ⊆ Set.range f)
    (b : Fin 4 →₀ ℕ) :
    p3SerreResidueCoefficient K b (tupleD2 z) = 0 := by
  exact p3SerreDualExponent_coefficient_tupleD2_eq_zero K z hz b id

/-- The monomial residue coefficients jointly detect the identity component
of a cochain whose Laurent support has total degree `-6` and all four
coordinates negative. -/
theorem p3SerreResidueCoefficient_jointly_detect_id
    (w : (Fin 4 → Fin 4) → LaurentPolynomial K)
    (hw : ∀ a ∈ (w id).coeff.support,
      totalDegree a = -6 ∧ negativeSupport a = Set.univ)
    (hzero : ∀ b : Fin 4 →₀ ℕ, b.degree = 2 →
      p3SerreResidueCoefficient K b w = 0) :
    w id = 0 := by
  ext a
  by_cases ha : a ∈ (w id).coeff.support
  · have haProps := hw a ha
    let b := p3SerrePolynomialExponent a
    have hb : b.degree = 2 :=
      p3SerrePolynomialExponent_degree_of_totalDegree_of_negativeSupport
        a haProps.1 haProps.2
    have hrecover : p3SerreDualExponent b = a :=
      p3SerreDualExponent_polynomialExponent_of_negativeSupport a haProps.2
    have h := hzero b hb
    change (w id).coeff (p3SerreDualExponent b) = 0 at h
    rwa [hrecover] at h
  · exact Finsupp.notMem_support_iff.mp ha

end LaurentCechExact
end PfaffianDescent
