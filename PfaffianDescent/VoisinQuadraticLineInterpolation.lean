import PfaffianDescent.FrameResolution
import AllCharacteristics.HomogeneousSpecialization
import PfaffianDescent.VoisinGenericSplitEtale

/-!
# Quadratic interpolation along an affine line

An affine polynomial of total degree at most two restricts along a line
through the origin to an ordinary univariate polynomial of degree at most
two. Three distinct zeros therefore annihilate that entire restriction.
-/

namespace PfaffianDescent

open MvPolynomial Polynomial

universe u

noncomputable def affineQuadraticScalePolynomial
    {L : Type u} [Field L]
    (Q : MvPolynomial (Fin 3) L) (v : Fin 3 → L) : Polynomial L :=
  Polynomial.C ((homogeneousComponent 0 Q).eval v) +
    Polynomial.C ((homogeneousComponent 1 Q).eval v) * Polynomial.X +
      Polynomial.C ((homogeneousComponent 2 Q).eval v) * Polynomial.X ^ 2

theorem affineQuadraticScalePolynomial_natDegree_le_two
    {L : Type u} [Field L]
    (Q : MvPolynomial (Fin 3) L) (v : Fin 3 → L) :
    (affineQuadraticScalePolynomial Q v).natDegree ≤ 2 := by
  unfold affineQuadraticScalePolynomial
  have h0 : (Polynomial.C ((homogeneousComponent 0 Q).eval v) : Polynomial L).natDegree ≤ 2 := by simp
  have h1 : (Polynomial.C ((homogeneousComponent 1 Q).eval v) * Polynomial.X : Polynomial L).natDegree ≤ 2 := by
    exact (natDegree_C_mul_le _ _).trans (by simp)
  have h2 : (Polynomial.C ((homogeneousComponent 2 Q).eval v) * Polynomial.X ^ 2 : Polynomial L).natDegree ≤ 2 := by
    exact (natDegree_C_mul_le _ _).trans (by simp)
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le h0 h1) h2

theorem affineQuadraticScalePolynomial_eval
    {L : Type u} [Field L]
    (Q : MvPolynomial (Fin 3) L) (hdegree : Q.totalDegree ≤ 2)
    (v : Fin 3 → L) (s : L) :
    (affineQuadraticScalePolynomial Q v).eval s = Q.eval (s • v) := by
  have hsum :
      homogeneousComponent 0 Q + homogeneousComponent 1 Q +
        homogeneousComponent 2 Q = Q := by
    simpa [Finset.sum_range_succ, add_assoc] using
      (homogeneousComponent_sum_of_bound Q 3 (by omega))
  have hcomp (d : ℕ) :
      (homogeneousComponent d Q).eval (s • v) =
        s ^ d * (homogeneousComponent d Q).eval v := by
    simpa only [MvPolynomial.eval₂_id] using
      (AllCharacteristics.eval₂_homogeneous_smul
        (homogeneousComponent d Q) (homogeneousComponent_isHomogeneous d Q)
        (RingHom.id L) v s)
  calc
    (affineQuadraticScalePolynomial Q v).eval s =
        (homogeneousComponent 0 Q).eval (s • v) +
          (homogeneousComponent 1 Q).eval (s • v) +
            (homogeneousComponent 2 Q).eval (s • v) := by
              rw [hcomp 0, hcomp 1, hcomp 2]
              simp only [affineQuadraticScalePolynomial, Polynomial.eval_add,
                Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
                Polynomial.eval_pow, pow_zero, pow_one, one_mul]
              ac_rfl
    _ = Q.eval (s • v) := by
      conv_rhs => rw [← hsum]
      simp only [MvPolynomial.eval_add]

theorem affine_quadratic_zero_on_line_of_three_distinct_roots
    {L : Type u} [Field L]
    (Q : MvPolynomial (Fin 3) L) (hdegree : Q.totalDegree ≤ 2)
    (v : Fin 3 → L) (t : Fin 3 → L)
    (hinj : Function.Injective t)
    (hroot : ∀ k, Q.eval (t k • v) = 0) :
    ∀ s : L, Q.eval (s • v) = 0 := by
  have hf : affineQuadraticScalePolynomial Q v = 0 :=
    quadratic_line_polynomial_zero_of_three_distinct_roots
      (affineQuadraticScalePolynomial Q v)
      (affineQuadraticScalePolynomial_natDegree_le_two Q v)
      t hinj (by
        intro k
        rw [affineQuadraticScalePolynomial_eval Q hdegree]
        exact hroot k)
  intro s
  rw [← affineQuadraticScalePolynomial_eval Q hdegree v s, hf]
  simp

end PfaffianDescent
