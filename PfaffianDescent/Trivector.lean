import PfaffianDescent.Basic
import Mathlib.Tactic.LinearCombination

/-! Explicit stable three-vector algebra. The coordinates are the twenty increasing
triples of {0,...,5}, in lexicographic order. Every identity is checked by Lean. -/
namespace PfaffianDescent
section Ring
variable {R : Type*} [CommRing R]

/-- Contraction of an alternating form with a three-vector. -/
def contract3 (A : Mat R 6) (p : Vec R 20) : Vec R 6 :=
  ![p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5,
    - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5,
    p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5,
    p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5,
    p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5,
    p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4]

/-- The quadratic endomorphism associated with a three-vector and the coordinate volume. -/
def hitchin (p : Vec R 20) : Mat R 6 :=
  !![p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10, 2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13, 2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16, 2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16, 2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16, 2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17;
    - 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7, p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10, - 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16, - 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16, - 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16, - 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17;
    2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7, 2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13, p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10, 2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13, 2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13, 2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14;
    - 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5, - 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11, - 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11, - p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10, - 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11, - 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12;
    2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4, 2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10, 2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10, 2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10, - p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10, 2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12;
    - 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4, - 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10, - 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10, - 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10, - 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11, - p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10]

/-- The quartic discriminant of a three-vector. -/
def trivectorDiscriminant (p : Vec R 20) : R :=
  (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4))))))

private theorem hitchin_square_0_0 (p : Vec R 20) :
    (hitchin p * hitchin p) 0 0 = trivectorDiscriminant p := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4)))))) = (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4))))))
  ring

private theorem hitchin_square_0_1 (p : Vec R 20) :
    (hitchin p * hitchin p) 0 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10)))))) = 0
  ring

private theorem hitchin_square_0_2 (p : Vec R 20) :
    (hitchin p * hitchin p) 0 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10)))))) = 0
  ring

private theorem hitchin_square_0_3 (p : Vec R 20) :
    (hitchin p * hitchin p) 0 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10)))))) = 0
  ring

private theorem hitchin_square_0_4 (p : Vec R 20) :
    (hitchin p * hitchin p) 0 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11)))))) = 0
  ring

private theorem hitchin_square_0_5 (p : Vec R 20) :
    (hitchin p * hitchin p) 0 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10)))))) = 0
  ring

private theorem hitchin_square_1_0 (p : Vec R 20) :
    (hitchin p * hitchin p) 1 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4)))))) = 0
  ring

private theorem hitchin_square_1_1 (p : Vec R 20) :
    (hitchin p * hitchin p) 1 1 = trivectorDiscriminant p := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) + ((- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) + ((- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) + ((- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10)))))) = (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4))))))
  ring

private theorem hitchin_square_1_2 (p : Vec R 20) :
    (hitchin p * hitchin p) 1 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) + ((- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) + ((- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) + ((- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10)))))) = 0
  ring

private theorem hitchin_square_1_3 (p : Vec R 20) :
    (hitchin p * hitchin p) 1 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) + ((- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) + ((- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) + ((- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) + ((- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10)))))) = 0
  ring

private theorem hitchin_square_1_4 (p : Vec R 20) :
    (hitchin p * hitchin p) 1 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) + ((- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) + ((- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) + ((- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) + ((- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11)))))) = 0
  ring

private theorem hitchin_square_1_5 (p : Vec R 20) :
    (hitchin p * hitchin p) 1 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) + ((- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) + ((- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) + ((- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) + ((- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10)))))) = 0
  ring

private theorem hitchin_square_2_0 (p : Vec R 20) :
    (hitchin p * hitchin p) 2 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4)))))) = 0
  ring

private theorem hitchin_square_2_1 (p : Vec R 20) :
    (hitchin p * hitchin p) 2 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) + ((2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) + ((2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) + ((2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) + ((2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10)))))) = 0
  ring

private theorem hitchin_square_2_2 (p : Vec R 20) :
    (hitchin p * hitchin p) 2 2 = trivectorDiscriminant p := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) + ((2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) + ((p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) + ((2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) + ((2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10)))))) = (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4))))))
  ring

private theorem hitchin_square_2_3 (p : Vec R 20) :
    (hitchin p * hitchin p) 2 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) + ((2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) + ((p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) + ((2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) + ((2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) + ((2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10)))))) = 0
  ring

private theorem hitchin_square_2_4 (p : Vec R 20) :
    (hitchin p * hitchin p) 2 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) + ((2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) + ((p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) + ((2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) + ((2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) + ((2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11)))))) = 0
  ring

private theorem hitchin_square_2_5 (p : Vec R 20) :
    (hitchin p * hitchin p) 2 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) + ((2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) + ((p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) + ((2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) + ((2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) + ((2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10)))))) = 0
  ring

private theorem hitchin_square_3_0 (p : Vec R 20) :
    (hitchin p * hitchin p) 3 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4)))))) = 0
  ring

private theorem hitchin_square_3_1 (p : Vec R 20) :
    (hitchin p * hitchin p) 3 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) + ((- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) + ((- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) + ((- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) + ((- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10)))))) = 0
  ring

private theorem hitchin_square_3_2 (p : Vec R 20) :
    (hitchin p * hitchin p) 3 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) + ((- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) + ((- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) + ((- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) + ((- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10)))))) = 0
  ring

private theorem hitchin_square_3_3 (p : Vec R 20) :
    (hitchin p * hitchin p) 3 3 = trivectorDiscriminant p := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) + ((- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) + ((- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) + ((- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) + ((- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) + ((- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10)))))) = (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4))))))
  ring

private theorem hitchin_square_3_4 (p : Vec R 20) :
    (hitchin p * hitchin p) 3 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) + ((- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) + ((- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) + ((- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) + ((- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) + ((- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11)))))) = 0
  ring

private theorem hitchin_square_3_5 (p : Vec R 20) :
    (hitchin p * hitchin p) 3 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) + ((- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) + ((- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) + ((- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) + ((- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) + ((- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10)))))) = 0
  ring

private theorem hitchin_square_4_0 (p : Vec R 20) :
    (hitchin p * hitchin p) 4 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4)))))) = 0
  ring

private theorem hitchin_square_4_1 (p : Vec R 20) :
    (hitchin p * hitchin p) 4 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) + ((2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) + ((2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) + ((- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) + ((2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10)))))) = 0
  ring

private theorem hitchin_square_4_2 (p : Vec R 20) :
    (hitchin p * hitchin p) 4 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) + ((2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) + ((2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) + ((- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) + ((2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10)))))) = 0
  ring

private theorem hitchin_square_4_3 (p : Vec R 20) :
    (hitchin p * hitchin p) 4 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) + ((2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) + ((2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) + ((2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) + ((- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) + ((2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10)))))) = 0
  ring

private theorem hitchin_square_4_4 (p : Vec R 20) :
    (hitchin p * hitchin p) 4 4 = trivectorDiscriminant p := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) + ((2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) + ((2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) + ((2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) + ((- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) + ((2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11)))))) = (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4))))))
  ring

private theorem hitchin_square_4_5 (p : Vec R 20) :
    (hitchin p * hitchin p) 4 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) + ((2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) + ((2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) + ((2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) + ((- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) + ((2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10)))))) = 0
  ring

private theorem hitchin_square_5_0 (p : Vec R 20) :
    (hitchin p * hitchin p) 5 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4)))))) = 0
  ring

private theorem hitchin_square_5_1 (p : Vec R 20) :
    (hitchin p * hitchin p) 5 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) + ((- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) + ((- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) + ((- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) + ((- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10)))))) = 0
  ring

private theorem hitchin_square_5_2 (p : Vec R 20) :
    (hitchin p * hitchin p) 5 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) + ((- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) + ((- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) + ((- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) + ((- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10)))))) = 0
  ring

private theorem hitchin_square_5_3 (p : Vec R 20) :
    (hitchin p * hitchin p) 5 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) + ((- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) + ((- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) + ((- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) + ((- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) + ((- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10)))))) = 0
  ring

private theorem hitchin_square_5_4 (p : Vec R 20) :
    (hitchin p * hitchin p) 5 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) + ((- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) + ((- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) + ((- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) + ((- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) + ((- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11)))))) = 0
  ring

private theorem hitchin_square_5_5 (p : Vec R 20) :
    (hitchin p * hitchin p) 5 5 = trivectorDiscriminant p := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) + ((- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) + ((- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) + ((- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) + ((- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) + ((- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10)))))) = (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4))))))
  ring

theorem hitchin_square (p : Vec R 20) :
    hitchin p * hitchin p = trivectorDiscriminant p • (1 : Mat R 6) := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using hitchin_square_0_0 p
  · simpa using hitchin_square_0_1 p
  · simpa using hitchin_square_0_2 p
  · simpa using hitchin_square_0_3 p
  · simpa using hitchin_square_0_4 p
  · simpa using hitchin_square_0_5 p
  · simpa using hitchin_square_1_0 p
  · simpa using hitchin_square_1_1 p
  · simpa using hitchin_square_1_2 p
  · simpa using hitchin_square_1_3 p
  · simpa using hitchin_square_1_4 p
  · simpa using hitchin_square_1_5 p
  · simpa using hitchin_square_2_0 p
  · simpa using hitchin_square_2_1 p
  · simpa using hitchin_square_2_2 p
  · simpa using hitchin_square_2_3 p
  · simpa using hitchin_square_2_4 p
  · simpa using hitchin_square_2_5 p
  · simpa using hitchin_square_3_0 p
  · simpa using hitchin_square_3_1 p
  · simpa using hitchin_square_3_2 p
  · simpa using hitchin_square_3_3 p
  · simpa using hitchin_square_3_4 p
  · simpa using hitchin_square_3_5 p
  · simpa using hitchin_square_4_0 p
  · simpa using hitchin_square_4_1 p
  · simpa using hitchin_square_4_2 p
  · simpa using hitchin_square_4_3 p
  · simpa using hitchin_square_4_4 p
  · simpa using hitchin_square_4_5 p
  · simpa using hitchin_square_5_0 p
  · simpa using hitchin_square_5_1 p
  · simpa using hitchin_square_5_2 p
  · simpa using hitchin_square_5_3 p
  · simpa using hitchin_square_5_4 p
  · simpa using hitchin_square_5_5 p

private theorem hitchin_compatible_0_0 (A : Mat R 6) (p : Vec R 20)
    (_hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 0 0 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((A 0 1) * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) + ((A 0 2) * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) + ((A 0 3) * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) + ((A 0 4) * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) + ((A 0 5) * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17))))))) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (0) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (- A 0 1) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (- A 0 2) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- A 0 3) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (- A 0 4) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- A 0 5))))))) = 0
  ring

private theorem hitchin_compatible_0_1 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 0 1 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((A 0 1) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((A 0 2) * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) + ((A 0 3) * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) + ((A 0 4) * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) + ((A 0 5) * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17))))))) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (A 0 1) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (0) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (- A 1 2) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- A 1 3) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (- A 1 4) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- A 1 5))))))) = 0
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (2) * p 19 * h2 + (-2) * p 18 * h3 + (2) * p 17 * h4 + (-2) * p 16 * h5

private theorem hitchin_compatible_0_2 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 0 2 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((A 0 1) * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) + ((A 0 2) * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((A 0 3) * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) + ((A 0 4) * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) + ((A 0 5) * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14))))))) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (A 0 2) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (A 1 2) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (0) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (- A 2 3) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (- A 2 4) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- A 2 5))))))) = 0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (-2) * p 19 * h1 + (2) * p 15 * h3 + (-2) * p 14 * h4 + (2) * p 13 * h5

private theorem hitchin_compatible_0_3 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 0 3 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((A 0 1) * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) + ((A 0 2) * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) + ((A 0 3) * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) + ((A 0 4) * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) + ((A 0 5) * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12))))))) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (A 0 3) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (A 1 3) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (A 2 3) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (0) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (- A 3 4) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- A 3 5))))))) = 0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (2) * p 18 * h1 + (-2) * p 15 * h2 + (2) * p 12 * h4 + (-2) * p 11 * h5

private theorem hitchin_compatible_0_4 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 0 4 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((A 0 1) * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) + ((A 0 2) * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) + ((A 0 3) * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) + ((A 0 4) * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) + ((A 0 5) * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12))))))) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (A 0 4) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (A 1 4) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (A 2 4) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (A 3 4) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (0) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (- A 4 5))))))) = 0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (-2) * p 17 * h1 + (2) * p 14 * h2 + (-2) * p 12 * h3 + (2) * p 10 * h5

private theorem hitchin_compatible_0_5 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 0 5 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((0) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) + ((A 0 1) * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) + ((A 0 2) * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) + ((A 0 3) * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) + ((A 0 4) * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) + ((A 0 5) * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10))))))) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (A 0 5) + ((2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) * (A 1 5) + ((2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) * (A 2 5) + ((2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) * (A 3 5) + ((2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) * (A 4 5) + ((2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17) * (0))))))) = 0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  linear_combination (2) * p 16 * h1 + (-2) * p 13 * h2 + (2) * p 11 * h3 + (-2) * p 10 * h4

private theorem hitchin_compatible_1_0 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 1 0 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 1) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((0) * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) + ((A 1 2) * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) + ((A 1 3) * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) + ((A 1 4) * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) + ((A 1 5) * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17))))))) + ((- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) * (0) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (- A 0 1) + ((- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) * (- A 0 2) + ((- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) * (- A 0 3) + ((- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) * (- A 0 4) + ((- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) * (- A 0 5))))))) = 0
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (-2) * p 19 * h2 + (2) * p 18 * h3 + (-2) * p 17 * h4 + (2) * p 16 * h5

private theorem hitchin_compatible_1_1 (A : Mat R 6) (p : Vec R 20)
    (_hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 1 1 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 1) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((0) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((A 1 2) * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) + ((A 1 3) * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) + ((A 1 4) * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) + ((A 1 5) * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17))))))) + ((- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) * (A 0 1) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (0) + ((- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) * (- A 1 2) + ((- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) * (- A 1 3) + ((- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) * (- A 1 4) + ((- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) * (- A 1 5))))))) = 0
  ring

private theorem hitchin_compatible_1_2 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 1 2 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 1) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((0) * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) + ((A 1 2) * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((A 1 3) * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) + ((A 1 4) * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) + ((A 1 5) * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14))))))) + ((- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) * (A 0 2) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (A 1 2) + ((- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) * (0) + ((- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) * (- A 2 3) + ((- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) * (- A 2 4) + ((- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) * (- A 2 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (2) * p 19 * h0 + (-2) * p 9 * h3 + (2) * p 8 * h4 + (-2) * p 7 * h5

private theorem hitchin_compatible_1_3 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 1 3 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 1) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((0) * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) + ((A 1 2) * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) + ((A 1 3) * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) + ((A 1 4) * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) + ((A 1 5) * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12))))))) + ((- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) * (A 0 3) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (A 1 3) + ((- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) * (A 2 3) + ((- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) * (0) + ((- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) * (- A 3 4) + ((- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) * (- A 3 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (-2) * p 18 * h0 + (2) * p 9 * h2 + (-2) * p 6 * h4 + (2) * p 5 * h5

private theorem hitchin_compatible_1_4 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 1 4 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 1) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((0) * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) + ((A 1 2) * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) + ((A 1 3) * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) + ((A 1 4) * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) + ((A 1 5) * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12))))))) + ((- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) * (A 0 4) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (A 1 4) + ((- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) * (A 2 4) + ((- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) * (A 3 4) + ((- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) * (0) + ((- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) * (- A 4 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (2) * p 17 * h0 + (-2) * p 8 * h2 + (2) * p 6 * h3 + (-2) * p 4 * h5

private theorem hitchin_compatible_1_5 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 1 5 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 1) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) + ((0) * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) + ((A 1 2) * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) + ((A 1 3) * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) + ((A 1 4) * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) + ((A 1 5) * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10))))))) + ((- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) * (A 0 5) + ((p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (A 1 5) + ((- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) * (A 2 5) + ((- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) * (A 3 5) + ((- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) * (A 4 5) + ((- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17) * (0))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  linear_combination (-2) * p 16 * h0 + (2) * p 7 * h2 + (-2) * p 5 * h3 + (2) * p 4 * h4

private theorem hitchin_compatible_2_0 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 2 0 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 2) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((- A 1 2) * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) + ((0) * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) + ((A 2 3) * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) + ((A 2 4) * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) + ((A 2 5) * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17))))))) + ((2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) * (0) + ((2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) * (- A 0 1) + ((p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (- A 0 2) + ((2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) * (- A 0 3) + ((2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) * (- A 0 4) + ((2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) * (- A 0 5))))))) = 0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (2) * p 19 * h1 + (-2) * p 15 * h3 + (2) * p 14 * h4 + (-2) * p 13 * h5

private theorem hitchin_compatible_2_1 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 2 1 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 2) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((- A 1 2) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((0) * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) + ((A 2 3) * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) + ((A 2 4) * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) + ((A 2 5) * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17))))))) + ((2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) * (A 0 1) + ((2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) * (0) + ((p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (- A 1 2) + ((2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) * (- A 1 3) + ((2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) * (- A 1 4) + ((2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) * (- A 1 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (-2) * p 19 * h0 + (2) * p 9 * h3 + (-2) * p 8 * h4 + (2) * p 7 * h5

private theorem hitchin_compatible_2_2 (A : Mat R 6) (p : Vec R 20)
    (_hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 2 2 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 2) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((- A 1 2) * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) + ((0) * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((A 2 3) * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) + ((A 2 4) * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) + ((A 2 5) * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14))))))) + ((2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) * (A 0 2) + ((2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) * (A 1 2) + ((p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (0) + ((2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) * (- A 2 3) + ((2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) * (- A 2 4) + ((2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) * (- A 2 5))))))) = 0
  ring

private theorem hitchin_compatible_2_3 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 2 3 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 2) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((- A 1 2) * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) + ((0) * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) + ((A 2 3) * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) + ((A 2 4) * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) + ((A 2 5) * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12))))))) + ((2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) * (A 0 3) + ((2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) * (A 1 3) + ((p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (A 2 3) + ((2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) * (0) + ((2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) * (- A 3 4) + ((2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) * (- A 3 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (2) * p 15 * h0 + (-2) * p 9 * h1 + (2) * p 3 * h4 + (-2) * p 2 * h5

private theorem hitchin_compatible_2_4 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 2 4 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 2) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((- A 1 2) * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) + ((0) * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) + ((A 2 3) * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) + ((A 2 4) * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) + ((A 2 5) * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12))))))) + ((2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) * (A 0 4) + ((2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) * (A 1 4) + ((p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (A 2 4) + ((2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) * (A 3 4) + ((2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) * (0) + ((2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) * (- A 4 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (-2) * p 14 * h0 + (2) * p 8 * h1 + (-2) * p 3 * h3 + (2) * p 1 * h5

private theorem hitchin_compatible_2_5 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 2 5 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 2) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) + ((- A 1 2) * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) + ((0) * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) + ((A 2 3) * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) + ((A 2 4) * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) + ((A 2 5) * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10))))))) + ((2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) * (A 0 5) + ((2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) * (A 1 5) + ((p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) * (A 2 5) + ((2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) * (A 3 5) + ((2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) * (A 4 5) + ((2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14) * (0))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  linear_combination (2) * p 13 * h0 + (-2) * p 7 * h1 + (2) * p 2 * h3 + (-2) * p 1 * h4

private theorem hitchin_compatible_3_0 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 3 0 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 3) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((- A 1 3) * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) + ((- A 2 3) * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) + ((0) * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) + ((A 3 4) * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) + ((A 3 5) * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17))))))) + ((- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) * (0) + ((- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) * (- A 0 1) + ((- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) * (- A 0 2) + ((- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) * (- A 0 3) + ((- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) * (- A 0 4) + ((- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) * (- A 0 5))))))) = 0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (-2) * p 18 * h1 + (2) * p 15 * h2 + (-2) * p 12 * h4 + (2) * p 11 * h5

private theorem hitchin_compatible_3_1 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 3 1 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 3) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((- A 1 3) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((- A 2 3) * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) + ((0) * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) + ((A 3 4) * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) + ((A 3 5) * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17))))))) + ((- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) * (A 0 1) + ((- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) * (0) + ((- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) * (- A 1 2) + ((- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) * (- A 1 3) + ((- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) * (- A 1 4) + ((- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) * (- A 1 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (2) * p 18 * h0 + (-2) * p 9 * h2 + (2) * p 6 * h4 + (-2) * p 5 * h5

private theorem hitchin_compatible_3_2 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 3 2 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 3) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((- A 1 3) * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) + ((- A 2 3) * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((0) * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) + ((A 3 4) * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) + ((A 3 5) * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14))))))) + ((- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) * (A 0 2) + ((- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) * (A 1 2) + ((- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) * (0) + ((- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) * (- A 2 3) + ((- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) * (- A 2 4) + ((- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) * (- A 2 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (-2) * p 15 * h0 + (2) * p 9 * h1 + (-2) * p 3 * h4 + (2) * p 2 * h5

private theorem hitchin_compatible_3_3 (A : Mat R 6) (p : Vec R 20)
    (_hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 3 3 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 3) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((- A 1 3) * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) + ((- A 2 3) * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) + ((0) * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) + ((A 3 4) * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) + ((A 3 5) * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12))))))) + ((- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) * (A 0 3) + ((- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) * (A 1 3) + ((- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) * (A 2 3) + ((- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) * (0) + ((- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) * (- A 3 4) + ((- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) * (- A 3 5))))))) = 0
  ring

private theorem hitchin_compatible_3_4 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 3 4 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 3) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((- A 1 3) * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) + ((- A 2 3) * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) + ((0) * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) + ((A 3 4) * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) + ((A 3 5) * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12))))))) + ((- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) * (A 0 4) + ((- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) * (A 1 4) + ((- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) * (A 2 4) + ((- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) * (A 3 4) + ((- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) * (0) + ((- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) * (- A 4 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (2) * p 12 * h0 + (-2) * p 6 * h1 + (2) * p 3 * h2 + (-2) * p 0 * h5

private theorem hitchin_compatible_3_5 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 3 5 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 3) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) + ((- A 1 3) * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) + ((- A 2 3) * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) + ((0) * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) + ((A 3 4) * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) + ((A 3 5) * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10))))))) + ((- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) * (A 0 5) + ((- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) * (A 1 5) + ((- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) * (A 2 5) + ((- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) * (A 3 5) + ((- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) * (A 4 5) + ((- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12) * (0))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  linear_combination (-2) * p 11 * h0 + (2) * p 5 * h1 + (-2) * p 2 * h2 + (2) * p 0 * h4

private theorem hitchin_compatible_4_0 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 4 0 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 4) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((- A 1 4) * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) + ((- A 2 4) * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) + ((- A 3 4) * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) + ((0) * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) + ((A 4 5) * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17))))))) + ((2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) * (0) + ((2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) * (- A 0 1) + ((2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) * (- A 0 2) + ((2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) * (- A 0 3) + ((- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) * (- A 0 4) + ((2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) * (- A 0 5))))))) = 0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (2) * p 17 * h1 + (-2) * p 14 * h2 + (2) * p 12 * h3 + (-2) * p 10 * h5

private theorem hitchin_compatible_4_1 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 4 1 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 4) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((- A 1 4) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((- A 2 4) * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) + ((- A 3 4) * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) + ((0) * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) + ((A 4 5) * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17))))))) + ((2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) * (A 0 1) + ((2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) * (0) + ((2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) * (- A 1 2) + ((2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) * (- A 1 3) + ((- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) * (- A 1 4) + ((2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) * (- A 1 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (-2) * p 17 * h0 + (2) * p 8 * h2 + (-2) * p 6 * h3 + (2) * p 4 * h5

private theorem hitchin_compatible_4_2 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 4 2 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 4) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((- A 1 4) * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) + ((- A 2 4) * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((- A 3 4) * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) + ((0) * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) + ((A 4 5) * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14))))))) + ((2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) * (A 0 2) + ((2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) * (A 1 2) + ((2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) * (0) + ((2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) * (- A 2 3) + ((- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) * (- A 2 4) + ((2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) * (- A 2 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (2) * p 14 * h0 + (-2) * p 8 * h1 + (2) * p 3 * h3 + (-2) * p 1 * h5

private theorem hitchin_compatible_4_3 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 4 3 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 4) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((- A 1 4) * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) + ((- A 2 4) * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) + ((- A 3 4) * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) + ((0) * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) + ((A 4 5) * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12))))))) + ((2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) * (A 0 3) + ((2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) * (A 1 3) + ((2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) * (A 2 3) + ((2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) * (0) + ((- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) * (- A 3 4) + ((2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) * (- A 3 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h5 := congrFun hc 5
  change p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4 = 0 at h5
  linear_combination (-2) * p 12 * h0 + (2) * p 6 * h1 + (-2) * p 3 * h2 + (2) * p 0 * h5

private theorem hitchin_compatible_4_4 (A : Mat R 6) (p : Vec R 20)
    (_hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 4 4 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 4) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((- A 1 4) * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) + ((- A 2 4) * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) + ((- A 3 4) * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) + ((0) * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) + ((A 4 5) * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12))))))) + ((2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) * (A 0 4) + ((2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) * (A 1 4) + ((2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) * (A 2 4) + ((2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) * (A 3 4) + ((- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) * (0) + ((2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) * (- A 4 5))))))) = 0
  ring

private theorem hitchin_compatible_4_5 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 4 5 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 4) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) + ((- A 1 4) * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) + ((- A 2 4) * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) + ((- A 3 4) * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) + ((0) * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) + ((A 4 5) * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10))))))) + ((2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) * (A 0 5) + ((2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) * (A 1 5) + ((2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) * (A 2 5) + ((2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) * (A 3 5) + ((- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) * (A 4 5) + ((2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12) * (0))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  linear_combination (2) * p 10 * h0 + (-2) * p 4 * h1 + (2) * p 1 * h2 + (-2) * p 0 * h3

private theorem hitchin_compatible_5_0 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 5 0 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 5) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10) + ((- A 1 5) * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13) + ((- A 2 5) * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16) + ((- A 3 5) * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16) + ((- A 4 5) * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16) + ((0) * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17))))))) + ((- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) * (0) + ((- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) * (- A 0 1) + ((- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) * (- A 0 2) + ((- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) * (- A 0 3) + ((- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) * (- A 0 4) + ((- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (- A 0 5))))))) = 0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  linear_combination (-2) * p 16 * h1 + (2) * p 13 * h2 + (-2) * p 11 * h3 + (2) * p 10 * h4

private theorem hitchin_compatible_5_1 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 5 1 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 5) * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7) + ((- A 1 5) * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((- A 2 5) * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16) + ((- A 3 5) * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16) + ((- A 4 5) * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16) + ((0) * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17))))))) + ((- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) * (A 0 1) + ((- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) * (0) + ((- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) * (- A 1 2) + ((- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) * (- A 1 3) + ((- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) * (- A 1 4) + ((- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (- A 1 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  linear_combination (2) * p 16 * h0 + (-2) * p 7 * h2 + (2) * p 5 * h3 + (-2) * p 4 * h4

private theorem hitchin_compatible_5_2 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 5 2 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 5) * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7) + ((- A 1 5) * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13) + ((- A 2 5) * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10) + ((- A 3 5) * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13) + ((- A 4 5) * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13) + ((0) * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14))))))) + ((- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) * (A 0 2) + ((- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) * (A 1 2) + ((- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) * (0) + ((- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) * (- A 2 3) + ((- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) * (- A 2 4) + ((- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (- A 2 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  linear_combination (-2) * p 13 * h0 + (2) * p 7 * h1 + (-2) * p 2 * h3 + (2) * p 1 * h4

private theorem hitchin_compatible_5_3 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 5 3 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 5) * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5) + ((- A 1 5) * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11) + ((- A 2 5) * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11) + ((- A 3 5) * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10) + ((- A 4 5) * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11) + ((0) * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12))))))) + ((- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) * (A 0 3) + ((- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) * (A 1 3) + ((- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) * (A 2 3) + ((- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) * (0) + ((- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) * (- A 3 4) + ((- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (- A 3 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h4 := congrFun hc 4
  change p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5 = 0 at h4
  linear_combination (2) * p 11 * h0 + (-2) * p 5 * h1 + (2) * p 2 * h2 + (-2) * p 0 * h4

private theorem hitchin_compatible_5_4 (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 5 4 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 5) * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4) + ((- A 1 5) * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10) + ((- A 2 5) * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10) + ((- A 3 5) * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10) + ((- A 4 5) * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10) + ((0) * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12))))))) + ((- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) * (A 0 4) + ((- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) * (A 1 4) + ((- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) * (A 2 4) + ((- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) * (A 3 4) + ((- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) * (0) + ((- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (- A 4 5))))))) = 0
  have h0 := congrFun hc 0
  change p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5 = 0 at h0
  have h1 := congrFun hc 1
  change - p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5 = 0 at h1
  have h2 := congrFun hc 2
  change p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5 = 0 at h2
  have h3 := congrFun hc 3
  change p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5 = 0 at h3
  linear_combination (-2) * p 10 * h0 + (2) * p 4 * h1 + (-2) * p 1 * h2 + (2) * p 0 * h3

private theorem hitchin_compatible_5_5 (A : Mat R 6) (p : Vec R 20)
    (_hc : contract3 A p = 0) :
    (skew6 A * (hitchin p).transpose + hitchin p * skew6 A) 5 5 = 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change ((- A 0 5) * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) + ((- A 1 5) * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) + ((- A 2 5) * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) + ((- A 3 5) * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) + ((- A 4 5) * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) + ((0) * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10))))))) + ((- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4) * (A 0 5) + ((- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10) * (A 1 5) + ((- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10) * (A 2 5) + ((- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10) * (A 3 5) + ((- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11) * (A 4 5) + ((- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10) * (0))))))) = 0
  ring

theorem hitchin_compatible_skew (A : Mat R 6) (p : Vec R 20)
    (hc : contract3 A p = 0) :
    skew6 A * (hitchin p).transpose + hitchin p * skew6 A = 0 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact hitchin_compatible_0_0 A p hc
  · exact hitchin_compatible_0_1 A p hc
  · exact hitchin_compatible_0_2 A p hc
  · exact hitchin_compatible_0_3 A p hc
  · exact hitchin_compatible_0_4 A p hc
  · exact hitchin_compatible_0_5 A p hc
  · exact hitchin_compatible_1_0 A p hc
  · exact hitchin_compatible_1_1 A p hc
  · exact hitchin_compatible_1_2 A p hc
  · exact hitchin_compatible_1_3 A p hc
  · exact hitchin_compatible_1_4 A p hc
  · exact hitchin_compatible_1_5 A p hc
  · exact hitchin_compatible_2_0 A p hc
  · exact hitchin_compatible_2_1 A p hc
  · exact hitchin_compatible_2_2 A p hc
  · exact hitchin_compatible_2_3 A p hc
  · exact hitchin_compatible_2_4 A p hc
  · exact hitchin_compatible_2_5 A p hc
  · exact hitchin_compatible_3_0 A p hc
  · exact hitchin_compatible_3_1 A p hc
  · exact hitchin_compatible_3_2 A p hc
  · exact hitchin_compatible_3_3 A p hc
  · exact hitchin_compatible_3_4 A p hc
  · exact hitchin_compatible_3_5 A p hc
  · exact hitchin_compatible_4_0 A p hc
  · exact hitchin_compatible_4_1 A p hc
  · exact hitchin_compatible_4_2 A p hc
  · exact hitchin_compatible_4_3 A p hc
  · exact hitchin_compatible_4_4 A p hc
  · exact hitchin_compatible_4_5 A p hc
  · exact hitchin_compatible_5_0 A p hc
  · exact hitchin_compatible_5_1 A p hc
  · exact hitchin_compatible_5_2 A p hc
  · exact hitchin_compatible_5_3 A p hc
  · exact hitchin_compatible_5_4 A p hc
  · exact hitchin_compatible_5_5 A p hc

theorem hitchin_compatible (A : Mat R 6) (hA : IsAlternating A)
    (p : Vec R 20) (hc : contract3 A p = 0) :
    A * (hitchin p).transpose + hitchin p * A = 0 := by
  simpa only [skew6_eq A hA] using hitchin_compatible_skew A p hc

private theorem hitchin_smul_0_0 (c : R) (p : Vec R 20) :
    hitchin (c • p) 0 0 = c^2 * hitchin p 0 0 := by
  change (c * p 0) * (c * p 19) - (c * p 1) * (c * p 18) + (c * p 2) * (c * p 17) - (c * p 3) * (c * p 16) + (c * p 4) * (c * p 15) - (c * p 5) * (c * p 14) + (c * p 6) * (c * p 13) + (c * p 7) * (c * p 12) - (c * p 8) * (c * p 11) + (c * p 9) * (c * p 10) = c^2 * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 + p 7 * p 12 - p 8 * p 11 + p 9 * p 10)
  ring

private theorem hitchin_smul_0_1 (c : R) (p : Vec R 20) :
    hitchin (c • p) 0 1 = c^2 * hitchin p 0 1 := by
  change 2 * (c * p 10) * (c * p 15) - 2 * (c * p 11) * (c * p 14) + 2 * (c * p 12) * (c * p 13) = c^2 * (2 * p 10 * p 15 - 2 * p 11 * p 14 + 2 * p 12 * p 13)
  ring

private theorem hitchin_smul_0_2 (c : R) (p : Vec R 20) :
    hitchin (c • p) 0 2 = c^2 * hitchin p 0 2 := by
  change 2 * (c * p 10) * (c * p 18) - 2 * (c * p 11) * (c * p 17) + 2 * (c * p 12) * (c * p 16) = c^2 * (2 * p 10 * p 18 - 2 * p 11 * p 17 + 2 * p 12 * p 16)
  ring

private theorem hitchin_smul_0_3 (c : R) (p : Vec R 20) :
    hitchin (c • p) 0 3 = c^2 * hitchin p 0 3 := by
  change 2 * (c * p 10) * (c * p 19) - 2 * (c * p 13) * (c * p 17) + 2 * (c * p 14) * (c * p 16) = c^2 * (2 * p 10 * p 19 - 2 * p 13 * p 17 + 2 * p 14 * p 16)
  ring

private theorem hitchin_smul_0_4 (c : R) (p : Vec R 20) :
    hitchin (c • p) 0 4 = c^2 * hitchin p 0 4 := by
  change 2 * (c * p 11) * (c * p 19) - 2 * (c * p 13) * (c * p 18) + 2 * (c * p 15) * (c * p 16) = c^2 * (2 * p 11 * p 19 - 2 * p 13 * p 18 + 2 * p 15 * p 16)
  ring

private theorem hitchin_smul_0_5 (c : R) (p : Vec R 20) :
    hitchin (c • p) 0 5 = c^2 * hitchin p 0 5 := by
  change 2 * (c * p 12) * (c * p 19) - 2 * (c * p 14) * (c * p 18) + 2 * (c * p 15) * (c * p 17) = c^2 * (2 * p 12 * p 19 - 2 * p 14 * p 18 + 2 * p 15 * p 17)
  ring

private theorem hitchin_smul_1_0 (c : R) (p : Vec R 20) :
    hitchin (c • p) 1 0 = c^2 * hitchin p 1 0 := by
  change - 2 * (c * p 4) * (c * p 9) + 2 * (c * p 5) * (c * p 8) - 2 * (c * p 6) * (c * p 7) = c^2 * (- 2 * p 4 * p 9 + 2 * p 5 * p 8 - 2 * p 6 * p 7)
  ring

private theorem hitchin_smul_1_1 (c : R) (p : Vec R 20) :
    hitchin (c • p) 1 1 = c^2 * hitchin p 1 1 := by
  change (c * p 0) * (c * p 19) - (c * p 1) * (c * p 18) + (c * p 2) * (c * p 17) - (c * p 3) * (c * p 16) - (c * p 4) * (c * p 15) + (c * p 5) * (c * p 14) - (c * p 6) * (c * p 13) - (c * p 7) * (c * p 12) + (c * p 8) * (c * p 11) - (c * p 9) * (c * p 10) = c^2 * (p 0 * p 19 - p 1 * p 18 + p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 - p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10)
  ring

private theorem hitchin_smul_1_2 (c : R) (p : Vec R 20) :
    hitchin (c • p) 1 2 = c^2 * hitchin p 1 2 := by
  change - 2 * (c * p 4) * (c * p 18) + 2 * (c * p 5) * (c * p 17) - 2 * (c * p 6) * (c * p 16) = c^2 * (- 2 * p 4 * p 18 + 2 * p 5 * p 17 - 2 * p 6 * p 16)
  ring

private theorem hitchin_smul_1_3 (c : R) (p : Vec R 20) :
    hitchin (c • p) 1 3 = c^2 * hitchin p 1 3 := by
  change - 2 * (c * p 4) * (c * p 19) + 2 * (c * p 7) * (c * p 17) - 2 * (c * p 8) * (c * p 16) = c^2 * (- 2 * p 4 * p 19 + 2 * p 7 * p 17 - 2 * p 8 * p 16)
  ring

private theorem hitchin_smul_1_4 (c : R) (p : Vec R 20) :
    hitchin (c • p) 1 4 = c^2 * hitchin p 1 4 := by
  change - 2 * (c * p 5) * (c * p 19) + 2 * (c * p 7) * (c * p 18) - 2 * (c * p 9) * (c * p 16) = c^2 * (- 2 * p 5 * p 19 + 2 * p 7 * p 18 - 2 * p 9 * p 16)
  ring

private theorem hitchin_smul_1_5 (c : R) (p : Vec R 20) :
    hitchin (c • p) 1 5 = c^2 * hitchin p 1 5 := by
  change - 2 * (c * p 6) * (c * p 19) + 2 * (c * p 8) * (c * p 18) - 2 * (c * p 9) * (c * p 17) = c^2 * (- 2 * p 6 * p 19 + 2 * p 8 * p 18 - 2 * p 9 * p 17)
  ring

private theorem hitchin_smul_2_0 (c : R) (p : Vec R 20) :
    hitchin (c • p) 2 0 = c^2 * hitchin p 2 0 := by
  change 2 * (c * p 1) * (c * p 9) - 2 * (c * p 2) * (c * p 8) + 2 * (c * p 3) * (c * p 7) = c^2 * (2 * p 1 * p 9 - 2 * p 2 * p 8 + 2 * p 3 * p 7)
  ring

private theorem hitchin_smul_2_1 (c : R) (p : Vec R 20) :
    hitchin (c • p) 2 1 = c^2 * hitchin p 2 1 := by
  change 2 * (c * p 1) * (c * p 15) - 2 * (c * p 2) * (c * p 14) + 2 * (c * p 3) * (c * p 13) = c^2 * (2 * p 1 * p 15 - 2 * p 2 * p 14 + 2 * p 3 * p 13)
  ring

private theorem hitchin_smul_2_2 (c : R) (p : Vec R 20) :
    hitchin (c • p) 2 2 = c^2 * hitchin p 2 2 := by
  change (c * p 0) * (c * p 19) + (c * p 1) * (c * p 18) - (c * p 2) * (c * p 17) + (c * p 3) * (c * p 16) + (c * p 4) * (c * p 15) - (c * p 5) * (c * p 14) + (c * p 6) * (c * p 13) - (c * p 7) * (c * p 12) + (c * p 8) * (c * p 11) - (c * p 9) * (c * p 10) = c^2 * (p 0 * p 19 + p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 - p 5 * p 14 + p 6 * p 13 - p 7 * p 12 + p 8 * p 11 - p 9 * p 10)
  ring

private theorem hitchin_smul_2_3 (c : R) (p : Vec R 20) :
    hitchin (c • p) 2 3 = c^2 * hitchin p 2 3 := by
  change 2 * (c * p 1) * (c * p 19) - 2 * (c * p 7) * (c * p 14) + 2 * (c * p 8) * (c * p 13) = c^2 * (2 * p 1 * p 19 - 2 * p 7 * p 14 + 2 * p 8 * p 13)
  ring

private theorem hitchin_smul_2_4 (c : R) (p : Vec R 20) :
    hitchin (c • p) 2 4 = c^2 * hitchin p 2 4 := by
  change 2 * (c * p 2) * (c * p 19) - 2 * (c * p 7) * (c * p 15) + 2 * (c * p 9) * (c * p 13) = c^2 * (2 * p 2 * p 19 - 2 * p 7 * p 15 + 2 * p 9 * p 13)
  ring

private theorem hitchin_smul_2_5 (c : R) (p : Vec R 20) :
    hitchin (c • p) 2 5 = c^2 * hitchin p 2 5 := by
  change 2 * (c * p 3) * (c * p 19) - 2 * (c * p 8) * (c * p 15) + 2 * (c * p 9) * (c * p 14) = c^2 * (2 * p 3 * p 19 - 2 * p 8 * p 15 + 2 * p 9 * p 14)
  ring

private theorem hitchin_smul_3_0 (c : R) (p : Vec R 20) :
    hitchin (c • p) 3 0 = c^2 * hitchin p 3 0 := by
  change - 2 * (c * p 0) * (c * p 9) + 2 * (c * p 2) * (c * p 6) - 2 * (c * p 3) * (c * p 5) = c^2 * (- 2 * p 0 * p 9 + 2 * p 2 * p 6 - 2 * p 3 * p 5)
  ring

private theorem hitchin_smul_3_1 (c : R) (p : Vec R 20) :
    hitchin (c • p) 3 1 = c^2 * hitchin p 3 1 := by
  change - 2 * (c * p 0) * (c * p 15) + 2 * (c * p 2) * (c * p 12) - 2 * (c * p 3) * (c * p 11) = c^2 * (- 2 * p 0 * p 15 + 2 * p 2 * p 12 - 2 * p 3 * p 11)
  ring

private theorem hitchin_smul_3_2 (c : R) (p : Vec R 20) :
    hitchin (c • p) 3 2 = c^2 * hitchin p 3 2 := by
  change - 2 * (c * p 0) * (c * p 18) + 2 * (c * p 5) * (c * p 12) - 2 * (c * p 6) * (c * p 11) = c^2 * (- 2 * p 0 * p 18 + 2 * p 5 * p 12 - 2 * p 6 * p 11)
  ring

private theorem hitchin_smul_3_3 (c : R) (p : Vec R 20) :
    hitchin (c • p) 3 3 = c^2 * hitchin p 3 3 := by
  change - (c * p 0) * (c * p 19) - (c * p 1) * (c * p 18) - (c * p 2) * (c * p 17) + (c * p 3) * (c * p 16) + (c * p 4) * (c * p 15) + (c * p 5) * (c * p 14) - (c * p 6) * (c * p 13) + (c * p 7) * (c * p 12) - (c * p 8) * (c * p 11) - (c * p 9) * (c * p 10) = c^2 * (- p 0 * p 19 - p 1 * p 18 - p 2 * p 17 + p 3 * p 16 + p 4 * p 15 + p 5 * p 14 - p 6 * p 13 + p 7 * p 12 - p 8 * p 11 - p 9 * p 10)
  ring

private theorem hitchin_smul_3_4 (c : R) (p : Vec R 20) :
    hitchin (c • p) 3 4 = c^2 * hitchin p 3 4 := by
  change - 2 * (c * p 2) * (c * p 18) + 2 * (c * p 5) * (c * p 15) - 2 * (c * p 9) * (c * p 11) = c^2 * (- 2 * p 2 * p 18 + 2 * p 5 * p 15 - 2 * p 9 * p 11)
  ring

private theorem hitchin_smul_3_5 (c : R) (p : Vec R 20) :
    hitchin (c • p) 3 5 = c^2 * hitchin p 3 5 := by
  change - 2 * (c * p 3) * (c * p 18) + 2 * (c * p 6) * (c * p 15) - 2 * (c * p 9) * (c * p 12) = c^2 * (- 2 * p 3 * p 18 + 2 * p 6 * p 15 - 2 * p 9 * p 12)
  ring

private theorem hitchin_smul_4_0 (c : R) (p : Vec R 20) :
    hitchin (c • p) 4 0 = c^2 * hitchin p 4 0 := by
  change 2 * (c * p 0) * (c * p 8) - 2 * (c * p 1) * (c * p 6) + 2 * (c * p 3) * (c * p 4) = c^2 * (2 * p 0 * p 8 - 2 * p 1 * p 6 + 2 * p 3 * p 4)
  ring

private theorem hitchin_smul_4_1 (c : R) (p : Vec R 20) :
    hitchin (c • p) 4 1 = c^2 * hitchin p 4 1 := by
  change 2 * (c * p 0) * (c * p 14) - 2 * (c * p 1) * (c * p 12) + 2 * (c * p 3) * (c * p 10) = c^2 * (2 * p 0 * p 14 - 2 * p 1 * p 12 + 2 * p 3 * p 10)
  ring

private theorem hitchin_smul_4_2 (c : R) (p : Vec R 20) :
    hitchin (c • p) 4 2 = c^2 * hitchin p 4 2 := by
  change 2 * (c * p 0) * (c * p 17) - 2 * (c * p 4) * (c * p 12) + 2 * (c * p 6) * (c * p 10) = c^2 * (2 * p 0 * p 17 - 2 * p 4 * p 12 + 2 * p 6 * p 10)
  ring

private theorem hitchin_smul_4_3 (c : R) (p : Vec R 20) :
    hitchin (c • p) 4 3 = c^2 * hitchin p 4 3 := by
  change 2 * (c * p 1) * (c * p 17) - 2 * (c * p 4) * (c * p 14) + 2 * (c * p 8) * (c * p 10) = c^2 * (2 * p 1 * p 17 - 2 * p 4 * p 14 + 2 * p 8 * p 10)
  ring

private theorem hitchin_smul_4_4 (c : R) (p : Vec R 20) :
    hitchin (c • p) 4 4 = c^2 * hitchin p 4 4 := by
  change - (c * p 0) * (c * p 19) + (c * p 1) * (c * p 18) + (c * p 2) * (c * p 17) + (c * p 3) * (c * p 16) - (c * p 4) * (c * p 15) - (c * p 5) * (c * p 14) - (c * p 6) * (c * p 13) + (c * p 7) * (c * p 12) + (c * p 8) * (c * p 11) + (c * p 9) * (c * p 10) = c^2 * (- p 0 * p 19 + p 1 * p 18 + p 2 * p 17 + p 3 * p 16 - p 4 * p 15 - p 5 * p 14 - p 6 * p 13 + p 7 * p 12 + p 8 * p 11 + p 9 * p 10)
  ring

private theorem hitchin_smul_4_5 (c : R) (p : Vec R 20) :
    hitchin (c • p) 4 5 = c^2 * hitchin p 4 5 := by
  change 2 * (c * p 3) * (c * p 17) - 2 * (c * p 6) * (c * p 14) + 2 * (c * p 8) * (c * p 12) = c^2 * (2 * p 3 * p 17 - 2 * p 6 * p 14 + 2 * p 8 * p 12)
  ring

private theorem hitchin_smul_5_0 (c : R) (p : Vec R 20) :
    hitchin (c • p) 5 0 = c^2 * hitchin p 5 0 := by
  change - 2 * (c * p 0) * (c * p 7) + 2 * (c * p 1) * (c * p 5) - 2 * (c * p 2) * (c * p 4) = c^2 * (- 2 * p 0 * p 7 + 2 * p 1 * p 5 - 2 * p 2 * p 4)
  ring

private theorem hitchin_smul_5_1 (c : R) (p : Vec R 20) :
    hitchin (c • p) 5 1 = c^2 * hitchin p 5 1 := by
  change - 2 * (c * p 0) * (c * p 13) + 2 * (c * p 1) * (c * p 11) - 2 * (c * p 2) * (c * p 10) = c^2 * (- 2 * p 0 * p 13 + 2 * p 1 * p 11 - 2 * p 2 * p 10)
  ring

private theorem hitchin_smul_5_2 (c : R) (p : Vec R 20) :
    hitchin (c • p) 5 2 = c^2 * hitchin p 5 2 := by
  change - 2 * (c * p 0) * (c * p 16) + 2 * (c * p 4) * (c * p 11) - 2 * (c * p 5) * (c * p 10) = c^2 * (- 2 * p 0 * p 16 + 2 * p 4 * p 11 - 2 * p 5 * p 10)
  ring

private theorem hitchin_smul_5_3 (c : R) (p : Vec R 20) :
    hitchin (c • p) 5 3 = c^2 * hitchin p 5 3 := by
  change - 2 * (c * p 1) * (c * p 16) + 2 * (c * p 4) * (c * p 13) - 2 * (c * p 7) * (c * p 10) = c^2 * (- 2 * p 1 * p 16 + 2 * p 4 * p 13 - 2 * p 7 * p 10)
  ring

private theorem hitchin_smul_5_4 (c : R) (p : Vec R 20) :
    hitchin (c • p) 5 4 = c^2 * hitchin p 5 4 := by
  change - 2 * (c * p 2) * (c * p 16) + 2 * (c * p 5) * (c * p 13) - 2 * (c * p 7) * (c * p 11) = c^2 * (- 2 * p 2 * p 16 + 2 * p 5 * p 13 - 2 * p 7 * p 11)
  ring

private theorem hitchin_smul_5_5 (c : R) (p : Vec R 20) :
    hitchin (c • p) 5 5 = c^2 * hitchin p 5 5 := by
  change - (c * p 0) * (c * p 19) + (c * p 1) * (c * p 18) - (c * p 2) * (c * p 17) - (c * p 3) * (c * p 16) - (c * p 4) * (c * p 15) + (c * p 5) * (c * p 14) + (c * p 6) * (c * p 13) - (c * p 7) * (c * p 12) - (c * p 8) * (c * p 11) + (c * p 9) * (c * p 10) = c^2 * (- p 0 * p 19 + p 1 * p 18 - p 2 * p 17 - p 3 * p 16 - p 4 * p 15 + p 5 * p 14 + p 6 * p 13 - p 7 * p 12 - p 8 * p 11 + p 9 * p 10)
  ring

theorem hitchin_smul (c : R) (p : Vec R 20) :
    hitchin (c • p) = c^2 • hitchin p := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact hitchin_smul_0_0 c p
  · exact hitchin_smul_0_1 c p
  · exact hitchin_smul_0_2 c p
  · exact hitchin_smul_0_3 c p
  · exact hitchin_smul_0_4 c p
  · exact hitchin_smul_0_5 c p
  · exact hitchin_smul_1_0 c p
  · exact hitchin_smul_1_1 c p
  · exact hitchin_smul_1_2 c p
  · exact hitchin_smul_1_3 c p
  · exact hitchin_smul_1_4 c p
  · exact hitchin_smul_1_5 c p
  · exact hitchin_smul_2_0 c p
  · exact hitchin_smul_2_1 c p
  · exact hitchin_smul_2_2 c p
  · exact hitchin_smul_2_3 c p
  · exact hitchin_smul_2_4 c p
  · exact hitchin_smul_2_5 c p
  · exact hitchin_smul_3_0 c p
  · exact hitchin_smul_3_1 c p
  · exact hitchin_smul_3_2 c p
  · exact hitchin_smul_3_3 c p
  · exact hitchin_smul_3_4 c p
  · exact hitchin_smul_3_5 c p
  · exact hitchin_smul_4_0 c p
  · exact hitchin_smul_4_1 c p
  · exact hitchin_smul_4_2 c p
  · exact hitchin_smul_4_3 c p
  · exact hitchin_smul_4_4 c p
  · exact hitchin_smul_4_5 c p
  · exact hitchin_smul_5_0 c p
  · exact hitchin_smul_5_1 c p
  · exact hitchin_smul_5_2 c p
  · exact hitchin_smul_5_3 c p
  · exact hitchin_smul_5_4 c p
  · exact hitchin_smul_5_5 c p

theorem trivectorDiscriminant_smul (c : R) (p : Vec R 20) :
    trivectorDiscriminant (c • p) = c^4 * trivectorDiscriminant p := by
  rw [← hitchin_square_0_0, hitchin_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  change (c^2*c^2) * (hitchin p * hitchin p) 0 0 = c^4 * trivectorDiscriminant p
  rw [hitchin_square_0_0]
  ring

variable {S : Type*} [CommRing S]

theorem contract3_map (f : R →+* S) (A : Mat R 6) (p : Vec R 20) :
    contract3 (A.map f) (fun i => f (p i)) = fun i => f (contract3 A p i) := by
  funext i
  fin_cases i
  · change f (p 0) * f (A 1 2) + f (p 1) * f (A 1 3) + f (p 2) * f (A 1 4) + f (p 3) * f (A 1 5) + f (p 4) * f (A 2 3) + f (p 5) * f (A 2 4) + f (p 6) * f (A 2 5) + f (p 7) * f (A 3 4) + f (p 8) * f (A 3 5) + f (p 9) * f (A 4 5) = f (p 0 * A 1 2 + p 1 * A 1 3 + p 2 * A 1 4 + p 3 * A 1 5 + p 4 * A 2 3 + p 5 * A 2 4 + p 6 * A 2 5 + p 7 * A 3 4 + p 8 * A 3 5 + p 9 * A 4 5)
    simp only [map_add, map_sub, map_mul, map_neg]
  · change - f (p 0) * f (A 0 2) - f (p 1) * f (A 0 3) - f (p 2) * f (A 0 4) - f (p 3) * f (A 0 5) + f (p 10) * f (A 2 3) + f (p 11) * f (A 2 4) + f (p 12) * f (A 2 5) + f (p 13) * f (A 3 4) + f (p 14) * f (A 3 5) + f (p 15) * f (A 4 5) = f (- p 0 * A 0 2 - p 1 * A 0 3 - p 2 * A 0 4 - p 3 * A 0 5 + p 10 * A 2 3 + p 11 * A 2 4 + p 12 * A 2 5 + p 13 * A 3 4 + p 14 * A 3 5 + p 15 * A 4 5)
    simp only [map_add, map_sub, map_mul, map_neg]
  · change f (p 0) * f (A 0 1) - f (p 4) * f (A 0 3) - f (p 5) * f (A 0 4) - f (p 6) * f (A 0 5) - f (p 10) * f (A 1 3) - f (p 11) * f (A 1 4) - f (p 12) * f (A 1 5) + f (p 16) * f (A 3 4) + f (p 17) * f (A 3 5) + f (p 18) * f (A 4 5) = f (p 0 * A 0 1 - p 4 * A 0 3 - p 5 * A 0 4 - p 6 * A 0 5 - p 10 * A 1 3 - p 11 * A 1 4 - p 12 * A 1 5 + p 16 * A 3 4 + p 17 * A 3 5 + p 18 * A 4 5)
    simp only [map_add, map_sub, map_mul, map_neg]
  · change f (p 1) * f (A 0 1) + f (p 4) * f (A 0 2) - f (p 7) * f (A 0 4) - f (p 8) * f (A 0 5) + f (p 10) * f (A 1 2) - f (p 13) * f (A 1 4) - f (p 14) * f (A 1 5) - f (p 16) * f (A 2 4) - f (p 17) * f (A 2 5) + f (p 19) * f (A 4 5) = f (p 1 * A 0 1 + p 4 * A 0 2 - p 7 * A 0 4 - p 8 * A 0 5 + p 10 * A 1 2 - p 13 * A 1 4 - p 14 * A 1 5 - p 16 * A 2 4 - p 17 * A 2 5 + p 19 * A 4 5)
    simp only [map_add, map_sub, map_mul, map_neg]
  · change f (p 2) * f (A 0 1) + f (p 5) * f (A 0 2) + f (p 7) * f (A 0 3) - f (p 9) * f (A 0 5) + f (p 11) * f (A 1 2) + f (p 13) * f (A 1 3) - f (p 15) * f (A 1 5) + f (p 16) * f (A 2 3) - f (p 18) * f (A 2 5) - f (p 19) * f (A 3 5) = f (p 2 * A 0 1 + p 5 * A 0 2 + p 7 * A 0 3 - p 9 * A 0 5 + p 11 * A 1 2 + p 13 * A 1 3 - p 15 * A 1 5 + p 16 * A 2 3 - p 18 * A 2 5 - p 19 * A 3 5)
    simp only [map_add, map_sub, map_mul, map_neg]
  · change f (p 3) * f (A 0 1) + f (p 6) * f (A 0 2) + f (p 8) * f (A 0 3) + f (p 9) * f (A 0 4) + f (p 12) * f (A 1 2) + f (p 14) * f (A 1 3) + f (p 15) * f (A 1 4) + f (p 17) * f (A 2 3) + f (p 18) * f (A 2 4) + f (p 19) * f (A 3 4) = f (p 3 * A 0 1 + p 6 * A 0 2 + p 8 * A 0 3 + p 9 * A 0 4 + p 12 * A 1 2 + p 14 * A 1 3 + p 15 * A 1 4 + p 17 * A 2 3 + p 18 * A 2 4 + p 19 * A 3 4)
    simp only [map_add, map_sub, map_mul, map_neg]

theorem trivectorDiscriminant_map (f : R →+* S) (p : Vec R 20) :
    trivectorDiscriminant (fun i => f (p i)) = f (trivectorDiscriminant p) := by
  simp only [trivectorDiscriminant, map_add, map_sub, map_mul, map_neg, map_ofNat]

end Ring
end PfaffianDescent
