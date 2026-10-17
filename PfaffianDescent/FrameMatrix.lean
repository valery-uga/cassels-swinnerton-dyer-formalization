import PfaffianDescent.FrameCoordinateRing

namespace PfaffianDescent
open scoped BigOperators

section
variable {R : Type*} [CommRing R]

/-- The five quadratic relations of the projective frame, in arbitrary coordinates. -/
def frameQuadrics (x : Vec R 4) : Vec R 5 :=
  ![x 0*x 2-x 0*x 1, x 0*x 3-x 0*x 1, x 1*x 2-x 0*x 1, x 1*x 3-x 0*x 1, x 2*x 3-x 0*x 1]

/-- An explicit alternating middle matrix for the projective-frame resolution. -/
def frameMatrix (x : Vec R 4) : Mat R 5 :=
  !![0, -x 1, -x 3, 0, x 1;
    -(-x 1), 0, 0, x 2, -x 1;
    -(-x 3), 0, 0, x 0, -x 0;
    0, -(x 2), -(x 0), 0, x 0;
    -(x 1), -(-x 1), -(-x 0), -(x 0), 0]

theorem frameMatrix_alternating (x : Vec R 4) : IsAlternating (frameMatrix x) := by
  constructor
  · intro i; fin_cases i <;> rfl
  · intro i j; fin_cases i <;> fin_cases j <;> simp [frameMatrix]

/-- The middle matrix annihilates the column of quadratic generators. -/
theorem frameMatrix_mul_quadrics (x : Vec R 4) :
    (frameMatrix x).mulVec (frameQuadrics x) = 0 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  fin_cases i
  · change ((0)*(x 0*x 2-x 0*x 1) + ((-x 1)*(x 0*x 3-x 0*x 1) + ((-x 3)*(x 1*x 2-x 0*x 1) + ((0)*(x 1*x 3-x 0*x 1) + (x 1)*(x 2*x 3-x 0*x 1))))) = 0
    ring
  · change ((-(-x 1))*(x 0*x 2-x 0*x 1) + ((0)*(x 0*x 3-x 0*x 1) + ((0)*(x 1*x 2-x 0*x 1) + ((x 2)*(x 1*x 3-x 0*x 1) + (-x 1)*(x 2*x 3-x 0*x 1))))) = 0
    ring
  · change ((-(-x 3))*(x 0*x 2-x 0*x 1) + ((0)*(x 0*x 3-x 0*x 1) + ((0)*(x 1*x 2-x 0*x 1) + ((x 0)*(x 1*x 3-x 0*x 1) + (-x 0)*(x 2*x 3-x 0*x 1))))) = 0
    ring
  · change ((0)*(x 0*x 2-x 0*x 1) + ((-(x 2))*(x 0*x 3-x 0*x 1) + ((-(x 0))*(x 1*x 2-x 0*x 1) + ((0)*(x 1*x 3-x 0*x 1) + (x 0)*(x 2*x 3-x 0*x 1))))) = 0
    ring
  · change ((-(x 1))*(x 0*x 2-x 0*x 1) + ((-(-x 1))*(x 0*x 3-x 0*x 1) + ((-(-x 0))*(x 1*x 2-x 0*x 1) + ((-(x 0))*(x 1*x 3-x 0*x 1) + (0)*(x 2*x 3-x 0*x 1))))) = 0
    ring

/-- Augmentation by five linear-form values. -/
def frameAugmentedMatrix (x : Vec R 4) (l : Vec R 5) : Mat R 6 :=
  !![0, -x 1, -x 3, 0, x 1, l 0;
    -(-x 1), 0, 0, x 2, -x 1, l 1;
    -(-x 3), 0, 0, x 0, -x 0, l 2;
    0, -(x 2), -(x 0), 0, x 0, l 3;
    -(x 1), -(-x 1), -(-x 0), -(x 0), 0, l 4;
    -l 0, -l 1, -l 2, -l 3, -l 4, 0]

theorem frameAugmentedMatrix_alternating (x : Vec R 4) (l : Vec R 5) :
    IsAlternating (frameAugmentedMatrix x l) := by
  constructor
  · intro i; fin_cases i <;> rfl
  · intro i j; fin_cases i <;> fin_cases j <;> simp [frameAugmentedMatrix]

/-- The signed principal Pfaffians are exactly the five frame relations. -/
theorem frameAugmentedMatrix_pfaffian (x : Vec R 4) (l : Vec R 5) :
    pf6 (frameAugmentedMatrix x l) = ∑ i, l i * frameQuadrics x i := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-x 1) * ((x 0)*(l 4) - (-x 0)*(l 3) + (l 2)*(x 0)) - (-x 3) * ((x 2)*(l 4) - (-x 1)*(l 3) + (l 1)*(x 0)) + (0) * ((0)*(l 4) - (-x 1)*(l 2) + (l 1)*(-x 0)) - (x 1) * ((0)*(l 3) - (x 2)*(l 2) + (l 1)*(x 0)) + (l 0) * ((0)*(x 0) - (x 2)*(-x 0) + (-x 1)*(x 0)) = (l 0*(x 0*x 2-x 0*x 1) + (l 1*(x 0*x 3-x 0*x 1) + (l 2*(x 1*x 2-x 0*x 1) + (l 3*(x 1*x 3-x 0*x 1) + l 4*(x 2*x 3-x 0*x 1)))))
  ring

end

section
variable {K : Type*} [Field K]

lemma frameQuadrics_X : frameQuadrics (MvPolynomial.X : Vec (MvPolynomial (Fin 4) K) 4) =
    frameRelations (K := K) := rfl

end
end PfaffianDescent
