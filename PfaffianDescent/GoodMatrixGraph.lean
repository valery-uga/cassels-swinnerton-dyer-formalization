import PfaffianDescent.GoodIsotropicAffineChart
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.LinearCombination

namespace PfaffianDescent
section
variable (R : Type*) [CommRing R]

/-- The split graph coordinates used by the good fiber. -/
def goodMatrixGraphVector (T : Matrix (Fin 3) (Fin 3) R) (x : Fin 3 → R) :
    Fin 3 → Fin 2 → R := fun i => ![x i, (T.mulVec x) i]

def goodBlockEigenvalue : Fin 3 → R := ![1, 2, 3]

lemma goodMatrixGraphVector_basis (T : Matrix (Fin 3) (Fin 3) R) (j : Fin 3) :
    goodMatrixGraphVector R T (Pi.single j 1) = fun i => ![if i = j then 1 else 0, T i j] := by
  funext i k
  fin_cases k <;> simp [goodMatrixGraphVector, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma goodSymplecticForm_graph_basis (T : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    goodSymplecticForm R (goodMatrixGraphVector R T (Pi.single i 1))
      (goodMatrixGraphVector R T (Pi.single j 1)) = T i j - T j i := by
  rw [goodMatrixGraphVector_basis, goodMatrixGraphVector_basis, goodSymplecticForm_apply]
  simp

lemma goodSpectralForm_graph_basis (T : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    goodSymplecticForm R (goodMatrixGraphVector R T (Pi.single i 1))
      (goodSpectralOperator R (Fin 2 → R) (goodMatrixGraphVector R T (Pi.single j 1))) =
      goodBlockEigenvalue R i * T i j - goodBlockEigenvalue R j * T j i := by
  rw [goodMatrixGraphVector_basis, goodMatrixGraphVector_basis]
  fin_cases i <;> fin_cases j <;>
    simp [goodSymplecticForm_apply, goodSpectralOperator, goodBlockEigenvalue,
      Fin.sum_univ_three] <;> ring

lemma goodBlockEigenvalue_difference_unit (h2 : IsUnit (2 : R)) (i j : Fin 3) (hij : i ≠ j) :
    IsUnit (goodBlockEigenvalue R i - goodBlockEigenvalue R j) := by
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals norm_num [goodBlockEigenvalue]
  all_goals first | exact h2 | simpa using h2.neg

/-- Entrywise equations for the first two forms cut out precisely diagonal matrices. -/
theorem goodMatrixGraph_diagonal_of_entries (h2 : IsUnit (2 : R))
    (T : Matrix (Fin 3) (Fin 3) R)
    (h0 : ∀ i j, T i j - T j i = 0)
    (h1 : ∀ i j, goodBlockEigenvalue R i * T i j - goodBlockEigenvalue R j * T j i = 0) :
    T = Matrix.diagonal (fun i => T i i) := by
  have hz (i j : Fin 3) (hij : i ≠ j) : T i j = 0 := by
    apply (goodBlockEigenvalue_difference_unit R h2 i j hij).mul_right_eq_zero.mp
    linear_combination h1 i j - goodBlockEigenvalue R j * h0 i j
  funext i j
  by_cases hij : i = j
  · subst j; simp
  · simp [Matrix.diagonal, hij, hz i j hij]

/-- The first two isotropy conditions force a graph matrix to be diagonal over every
ring in which two is invertible, including nonreduced rings. -/
theorem goodMatrixGraph_diagonal (h2 : IsUnit (2 : R))
    (T : Matrix (Fin 3) (Fin 3) R)
    (h0 : ∀ x y, goodSymplecticForm R (goodMatrixGraphVector R T x)
      (goodMatrixGraphVector R T y) = 0)
    (h1 : ∀ x y, goodSymplecticForm R (goodMatrixGraphVector R T x)
      (goodSpectralOperator R (Fin 2 → R) (goodMatrixGraphVector R T y)) = 0) :
    T = Matrix.diagonal (fun i => T i i) := by
  apply goodMatrixGraph_diagonal_of_entries R h2 T
  · intro i j
    simpa only [goodSymplecticForm_graph_basis] using h0 (Pi.single i 1) (Pi.single j 1)
  · intro i j
    simpa only [goodSpectralForm_graph_basis] using h1 (Pi.single i 1) (Pi.single j 1)

lemma goodMatrixGraphVector_diagonal (u x : Fin 3 → R) :
    goodMatrixGraphVector R (Matrix.diagonal u) x = fun i => ![x i, x i * u i] := by
  funext i k
  fin_cases k <;> simp [goodMatrixGraphVector, Matrix.mulVec_diagonal, mul_comm]

/-- On the diagonal graph chart, the third matrix imposes exactly three equations. -/
theorem goodMatrixGraph_third_iff (u : Fin 3 → R) :
    (∀ x y, goodThirdBlockForm R (goodMatrixGraphVector R (Matrix.diagonal u) x)
      (goodMatrixGraphVector R (Matrix.diagonal u) y) = 0) ↔
      1 + u 0 * u 1 = 0 ∧ 1 + u 0 * u 2 = 0 ∧ 1 + 2 * u 1 * u 2 = 0 := by
  have he (x y : Fin 3 → R) :
      goodThirdBlockForm R (goodMatrixGraphVector R (Matrix.diagonal u) x)
        (goodMatrixGraphVector R (Matrix.diagonal u) y) =
        (1 + u 0 * u 1) * (x 0 * y 1 - x 1 * y 0) +
        (1 + u 0 * u 2) * (x 0 * y 2 - x 2 * y 0) +
        (1 + 2 * u 1 * u 2) * (x 1 * y 2 - x 2 * y 1) := by
    rw [goodMatrixGraphVector_diagonal, goodMatrixGraphVector_diagonal]
    simpa using goodThirdBlockForm_line_evaluation R (fun _ => 1) u x y
  constructor
  · intro h
    have ha := h ![1, 0, 0] ![0, 1, 0]
    have hb := h ![1, 0, 0] ![0, 0, 1]
    have hc := h ![0, 1, 0] ![0, 0, 1]
    rw [he] at ha hb hc
    exact ⟨by simpa using ha, by simpa using hb, by simpa using hc⟩
  · rintro ⟨ha, hb, hc⟩ x y
    rw [he, ha, hb, hc]
    simp

end
end PfaffianDescent
