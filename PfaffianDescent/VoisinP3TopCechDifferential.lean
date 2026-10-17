import PfaffianDescent.VoisinTwistCechLaurentDifferential
import PfaffianDescent.VoisinP3TopCechDetection

/-!
# The top projective Cech differential in Laurent coordinates

This identifies the degree-three differential of the raw four-chart Cech
complex with the explicit five-term tuple differential used by the residue
calculation.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial Opposite
open CategoryTheory.Limits
open scoped AddMonoidAlgebra BigOperators

universe u

namespace PfaffianDescent.ProjectiveNegativeTwist

open LaurentLocalization LaurentCechCore AwayCechExact

variable (K : Type u) [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Under the Laurent-coordinate realization, the raw Cech differential
from degree three to degree four is the five-term alternating tuple map. -/
lemma p3NegativeTwistCechTermToLaurent_d_three
    (m : ℕ) (x : (p3NegativeTwistCechComplex (K := K) m).X 3) :
    p3NegativeTwistCechTermToLaurent K m 4
        ((p3NegativeTwistCechComplex (K := K) m).d 3 4 x) =
      tupleD3 (p3NegativeTwistCechTermToLaurent K m 3 x) := by
  rw [p3NegativeTwistCechTermToLaurent_d K m 3 x]
  funext f
  have h0 : deleteTuple (0 : Fin 5) f = ![f 1, f 2, f 3, f 4] := by
    funext i
    fin_cases i <;> rfl
  have h1 : deleteTuple (1 : Fin 5) f = ![f 0, f 2, f 3, f 4] := by
    funext i
    fin_cases i <;> rfl
  have h2 : deleteTuple (2 : Fin 5) f = ![f 0, f 1, f 3, f 4] := by
    funext i
    fin_cases i <;> rfl
  have h3 : deleteTuple (3 : Fin 5) f = ![f 0, f 1, f 2, f 4] := by
    funext i
    fin_cases i <;> rfl
  have h4 : deleteTuple (4 : Fin 5) f = ![f 0, f 1, f 2, f 3] := by
    funext i
    fin_cases i <;> rfl
  simp [Fin.sum_univ_succ, tupleD3, sub_eq_add_neg, h0, h1, h2, h3, h4]
  norm_num
  simp only [add_assoc]

end PfaffianDescent.ProjectiveNegativeTwist
