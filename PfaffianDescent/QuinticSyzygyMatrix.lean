import PfaffianDescent.QuinticPresentation

namespace PfaffianDescent
open scoped BigOperators
section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The five-by-five alternating matrix in the explicit quintic presentation. -/
def quinticSyzygyMatrix (a : Vec R 5) (x : Vec R 4) : Mat R 5 :=
  (quinticMatrix a x 0).submatrix Fin.castSucc Fin.castSucc

lemma quinticSyzygyMatrix_alternating (a : Vec R 5) (x : Vec R 4) :
    IsAlternating (quinticSyzygyMatrix a x) := by
  exact ⟨fun i => (quinticMatrix_alternating a x 0).1 (Fin.castSucc i),
    fun i j => (quinticMatrix_alternating a x 0).2 (Fin.castSucc i) (Fin.castSucc j)⟩

lemma quinticQuadrics_map (f : R →+* S) (a : Vec R 5) (x : Vec R 4) (i : Fin 5) :
    f (quinticQuadrics a x i) = quinticQuadrics (f ∘ a) (f ∘ x) i := by
  fin_cases i <;> simp [quinticQuadrics]

lemma quinticSyzygyMatrix_map (f : R →+* S) (a : Vec R 5) (x : Vec R 4) :
    (quinticSyzygyMatrix a x).map f = quinticSyzygyMatrix (f ∘ a) (f ∘ x) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [quinticSyzygyMatrix, quinticMatrix]

/-- The quadratic Pfaffians give a vector in the kernel of the alternating matrix. -/
theorem quinticSyzygyMatrix_quadrics (a : Vec R 5) (x : Vec R 4) :
    (quinticSyzygyMatrix a x).mulVec (quinticQuadrics a x) = 0 := by
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (0) * (x 0 * x 2 - x 1^2) + ((a 3 * x 3 + a 0 * x 0) * (x 0 * x 3 - x 1 * x 2) + ((a 4 * x 3 + a 1 * x 0) * (x 1 * x 3 - x 2^2) + ((-x 3) * (x 2 * x 3 + a 4 * x 1 * x 3 + a 3 * x 0 * x 3 + a 2 * x 0 * x 2 + a 1 * x 0 * x 1 + a 0 * x 0^2) + ((x 2) * (x 3^2 + a 4 * x 2 * x 3 + a 3 * x 1 * x 3 + a 2 * x 0 * x 3 + a 1 * x 0 * x 2 + a 0 * x 0 * x 1))))) = 0
    ring
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (-(a 3 * x 3 + a 0 * x 0)) * (x 0 * x 2 - x 1^2) + ((0) * (x 0 * x 3 - x 1 * x 2) + ((x 3 + a 2 * x 0) * (x 1 * x 3 - x 2^2) + ((x 2) * (x 2 * x 3 + a 4 * x 1 * x 3 + a 3 * x 0 * x 3 + a 2 * x 0 * x 2 + a 1 * x 0 * x 1 + a 0 * x 0^2) + ((-x 1) * (x 3^2 + a 4 * x 2 * x 3 + a 3 * x 1 * x 3 + a 2 * x 0 * x 3 + a 1 * x 0 * x 2 + a 0 * x 0 * x 1))))) = 0
    ring
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (-(a 4 * x 3 + a 1 * x 0)) * (x 0 * x 2 - x 1^2) + ((-(x 3 + a 2 * x 0)) * (x 0 * x 3 - x 1 * x 2) + ((0) * (x 1 * x 3 - x 2^2) + ((-x 1) * (x 2 * x 3 + a 4 * x 1 * x 3 + a 3 * x 0 * x 3 + a 2 * x 0 * x 2 + a 1 * x 0 * x 1 + a 0 * x 0^2) + ((x 0) * (x 3^2 + a 4 * x 2 * x 3 + a 3 * x 1 * x 3 + a 2 * x 0 * x 3 + a 1 * x 0 * x 2 + a 0 * x 0 * x 1))))) = 0
    ring
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (-(-x 3)) * (x 0 * x 2 - x 1^2) + ((-(x 2)) * (x 0 * x 3 - x 1 * x 2) + ((-(-x 1)) * (x 1 * x 3 - x 2^2) + ((0) * (x 2 * x 3 + a 4 * x 1 * x 3 + a 3 * x 0 * x 3 + a 2 * x 0 * x 2 + a 1 * x 0 * x 1 + a 0 * x 0^2) + ((0) * (x 3^2 + a 4 * x 2 * x 3 + a 3 * x 1 * x 3 + a 2 * x 0 * x 3 + a 1 * x 0 * x 2 + a 0 * x 0 * x 1))))) = 0
    ring
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (-(x 2)) * (x 0 * x 2 - x 1^2) + ((-(-x 1)) * (x 0 * x 3 - x 1 * x 2) + ((-(x 0)) * (x 1 * x 3 - x 2^2) + ((-(0)) * (x 2 * x 3 + a 4 * x 1 * x 3 + a 3 * x 0 * x 3 + a 2 * x 0 * x 2 + a 1 * x 0 * x 1 + a 0 * x 0^2) + ((0) * (x 3^2 + a 4 * x 2 * x 3 + a 3 * x 1 * x 3 + a 2 * x 0 * x 3 + a 1 * x 0 * x 2 + a 0 * x 0 * x 1))))) = 0
    ring

end
end PfaffianDescent
