import PfaffianDescent.VoisinP3TopCechExact
import PfaffianDescent.VoisinP3TopCechDifferential

/-!
# Residue classification on the raw Cech complex of `O(-6)`

The explicit Laurent residue is transported back to the actual raw Cech
complex of the negative sixth twist on projective three-space.  On top
cocycles, simultaneous vanishing of all quadratic residues is equivalent to
being a degree-two Cech boundary.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped AddMonoidAlgebra BigOperators

universe u

namespace PfaffianDescent.ProjectiveNegativeTwist

open LaurentLocalization LaurentCechCore LaurentCechExact

variable (K : Type u) [Field K]

/-- The raw top-Cech residue functional paired with a quadratic monomial. -/
def p3NegativeSixRawResidue (b : Fin 4 →₀ ℕ) :
    (p3NegativeTwistCechComplex (K := K) 6).X 3 →+ K :=
  (p3SerreResidueCoefficient K b).comp
    (p3NegativeTwistCechTermToLaurent K 6 3)

@[simp]
lemma p3NegativeSixRawResidue_apply
    (b : Fin 4 →₀ ℕ)
    (w : (p3NegativeTwistCechComplex (K := K) 6).X 3) :
    p3NegativeSixRawResidue K b w =
      p3SerreResidueCoefficient K b
        (p3NegativeTwistCechTermToLaurent K 6 3 w) := rfl

/-- Every raw degree-two boundary has zero quadratic residues. -/
lemma p3NegativeSixRawResidue_boundary_eq_zero
    (z : (p3NegativeTwistCechComplex (K := K) 6).X 2)
    (b : Fin 4 →₀ ℕ) :
    p3NegativeSixRawResidue K b
        ((p3NegativeTwistCechComplex (K := K) 6).d 2 3 z) = 0 := by
  rw [p3NegativeSixRawResidue_apply,
    p3NegativeTwistCechTermToLaurent_d_two K 6 z]
  apply p3SerreResidueCoefficient_tupleD2_eq_zero
  intro f a ha
  exact (p3NegativeTwistCechTermToLaurent_support_properties K 6 2 z f a ha).2

/-- A top cocycle of the raw Cech complex of `O(-6)` with all quadratic
residues zero is a degree-two boundary. -/
theorem p3NegativeSixRawCocycle_is_boundary_of_residue_zero
    (w : (p3NegativeTwistCechComplex (K := K) 6).X 3)
    (hwcycle :
      (p3NegativeTwistCechComplex (K := K) 6).d 3 4 w = 0)
    (hres : ∀ b : Fin 4 →₀ ℕ, b.degree = 2 →
      p3NegativeSixRawResidue K b w = 0) :
    ∃ z : (p3NegativeTwistCechComplex (K := K) 6).X 2,
      (p3NegativeTwistCechComplex (K := K) 6).d 2 3 z = w := by
  let wL := p3NegativeTwistCechTermToLaurent K 6 3 w
  have hwL : ∀ f (a : LaurentLocalization.LaurentExponent),
      a ∈ (wL f).coeff.support →
      totalDegree a = -6 ∧ negativeSupport a ⊆ Set.range f := by
    intro f a ha
    simpa [wL] using
      p3NegativeTwistCechTermToLaurent_support_properties K 6 3 w f a ha
  have hdwL : ∀ f, tupleD3 wL f = 0 := by
    intro f
    rw [← congrFun (p3NegativeTwistCechTermToLaurent_d_three K 6 w) f,
      hwcycle]
    simp
  have hresL : ∀ b : Fin 4 →₀ ℕ, b.degree = 2 →
      p3SerreResidueCoefficient K b wL = 0 := by
    intro b hb
    exact hres b hb
  obtain ⟨zL, hzL, hdiff⟩ :=
    laurent_tuple_exact_three_of_degree_neg_six_of_residue_zero
      K wL hwL hdwL hresL
  obtain ⟨z, hz⟩ :=
    exists_p3NegativeTwistCechTermToLaurent_eq_of_support K 6 2 zL
      (by
        intro f a ha
        simpa using hzL f a ha)
  refine ⟨z, ?_⟩
  apply p3NegativeTwistCechTermToLaurent_injective K 6 3
  rw [p3NegativeTwistCechTermToLaurent_d_two K 6 z, hz]
  funext f
  exact hdiff f

/-- For a raw top cocycle of `O(-6)`, vanishing of all quadratic residues is
equivalent to membership in the image of the preceding Cech differential. -/
theorem p3NegativeSixRawCocycle_residue_zero_iff_boundary
    (w : (p3NegativeTwistCechComplex (K := K) 6).X 3)
    (hwcycle :
      (p3NegativeTwistCechComplex (K := K) 6).d 3 4 w = 0) :
    (∀ b : Fin 4 →₀ ℕ, b.degree = 2 →
        p3NegativeSixRawResidue K b w = 0) ↔
      ∃ z : (p3NegativeTwistCechComplex (K := K) 6).X 2,
        (p3NegativeTwistCechComplex (K := K) 6).d 2 3 z = w := by
  constructor
  · exact p3NegativeSixRawCocycle_is_boundary_of_residue_zero K w hwcycle
  · rintro ⟨z, rfl⟩ b _hb
    exact p3NegativeSixRawResidue_boundary_eq_zero K z b

end PfaffianDescent.ProjectiveNegativeTwist
