import PfaffianDescent.VoisinP3TopCechExact
import PfaffianDescent.VoisinP3TopCechDifferential

/-!
# Top Cech vanishing for `O(-3)` on projective three-space

There is no Laurent monomial of total degree `-3` whose four exponents are
all negative.  The explicit Laurent contraction therefore makes every raw
top Cech cocycle a boundary.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial
open scoped AddMonoidAlgebra BigOperators

universe u

namespace PfaffianDescent.ProjectiveNegativeTwist

open LaurentLocalization LaurentCechCore LaurentCechExact

variable (K : Type u) [Field K]

/-- Every raw degree-three Cech cocycle of `O(-3)` is a degree-two
boundary. -/
theorem p3NegativeThreeRawCocycle_is_boundary
    (w : (p3NegativeTwistCechComplex (K := K) 3).X 3)
    (hwcycle :
      (p3NegativeTwistCechComplex (K := K) 3).d 3 4 w = 0) :
    ∃ z : (p3NegativeTwistCechComplex (K := K) 3).X 2,
      (p3NegativeTwistCechComplex (K := K) 3).d 2 3 z = w := by
  let wL := p3NegativeTwistCechTermToLaurent K 3 3 w
  have hwL : ∀ f (a : LaurentLocalization.LaurentExponent),
      a ∈ (wL f).coeff.support →
      totalDegree a = -3 ∧ negativeSupport a ⊆ Set.range f := by
    intro f a ha
    simpa [wL] using
      p3NegativeTwistCechTermToLaurent_support_properties K 3 3 w f a ha
  have hdwL : ∀ f, tupleD3 wL f = 0 := by
    intro f
    rw [← congrFun (p3NegativeTwistCechTermToLaurent_d_three K 3 w) f,
      hwcycle]
    simp
  obtain ⟨zL, hzL, hdiff⟩ :=
    laurent_tuple_exact_three_of_degree_neg_three K wL hwL hdwL
  obtain ⟨z, hz⟩ :=
    exists_p3NegativeTwistCechTermToLaurent_eq_of_support K 3 2 zL
      (by
        intro f a ha
        simpa using hzL f a ha)
  refine ⟨z, ?_⟩
  apply p3NegativeTwistCechTermToLaurent_injective K 3 3
  rw [p3NegativeTwistCechTermToLaurent_d_two K 3 z, hz]
  funext f
  exact hdiff f

end PfaffianDescent.ProjectiveNegativeTwist
