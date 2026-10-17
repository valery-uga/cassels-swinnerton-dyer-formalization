import PfaffianDescent.GoodBlockForms

namespace PfaffianDescent
open LinearMap (BilinForm)
section
variable (R : Type*) [CommRing R]

/-- The third displayed form, expressed in the three two-dimensional blocks. -/
def goodThirdBlockForm : BilinForm R (Fin 3 → Fin 2 → R) :=
  (goodTriple 2 : Mat R 6).toBilin'.compl₁₂
    (goodBlockCoordinates R).symm.toLinearMap (goodBlockCoordinates R).symm.toLinearMap

lemma goodThirdBlockForm_pair01 (x y : Fin 2 → R) :
    goodThirdBlockForm R (Pi.single 0 x) (Pi.single 1 y) = x 0 * y 0 + x 1 * y 1 := by
  simp [goodThirdBlockForm, Matrix.toBilin'_apply, goodTriple, Fin.sum_univ_six,
    goodBlockCoordinates, Pi.single_apply]

lemma goodThirdBlockForm_pair02 (x y : Fin 2 → R) :
    goodThirdBlockForm R (Pi.single 0 x) (Pi.single 2 y) = x 0 * y 0 + x 1 * y 1 := by
  simp [goodThirdBlockForm, Matrix.toBilin'_apply, goodTriple, Fin.sum_univ_six,
    goodBlockCoordinates, Pi.single_apply]

lemma goodThirdBlockForm_pair12 (x y : Fin 2 → R) :
    goodThirdBlockForm R (Pi.single 1 x) (Pi.single 2 y) = x 0 * y 0 + 2 * x 1 * y 1 := by
  simp [goodThirdBlockForm, Matrix.toBilin'_apply, goodTriple, Fin.sum_univ_six,
    goodBlockCoordinates, Pi.single_apply]
  ring

/-- Evaluation on a direct sum of three lines gives exactly the three equations in the note. -/
lemma goodThirdBlockForm_line_evaluation (a b x y : Fin 3 → R) :
    goodThirdBlockForm R (fun i => ![x i * a i, x i * b i])
      (fun i => ![y i * a i, y i * b i]) =
      (a 0 * a 1 + b 0 * b 1) * (x 0 * y 1 - x 1 * y 0) +
      (a 0 * a 2 + b 0 * b 2) * (x 0 * y 2 - x 2 * y 0) +
      (a 1 * a 2 + 2 * b 1 * b 2) * (x 1 * y 2 - x 2 * y 1) := by
  simp [goodThirdBlockForm, Matrix.toBilin'_apply, goodTriple, Fin.sum_univ_six,
    goodBlockCoordinates]
  ring

/-- This is the actual third matrix in the original six coordinates. -/
lemma goodTriple_two_block_form (x y : Fin 6 → R) :
    (goodTriple 2 : Mat R 6).toBilin' x y =
      goodThirdBlockForm R (goodBlockCoordinates R x) (goodBlockCoordinates R y) := by
  simp [goodThirdBlockForm]

end
end PfaffianDescent
