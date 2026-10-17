import PfaffianDescent.QuinticPresentation

/-! Exact cubic reduction by the five quintic quadrics, with a five-dimensional remainder. -/
namespace PfaffianDescent
section
variable {R : Type*} [CommRing R]

/-- All degree-three monomials in four variables, in lexicographic order. -/
def cubicMonomials (x : Vec R 4) : Vec R 20 :=
  ![x 0 * x 0 * x 0, x 0 * x 0 * x 1, x 0 * x 0 * x 2, x 0 * x 0 * x 3, x 0 * x 1 * x 1, x 0 * x 1 * x 2, x 0 * x 1 * x 3, x 0 * x 2 * x 2, x 0 * x 2 * x 3, x 0 * x 3 * x 3, x 1 * x 1 * x 1, x 1 * x 1 * x 2, x 1 * x 1 * x 3, x 1 * x 2 * x 2, x 1 * x 2 * x 3, x 1 * x 3 * x 3, x 2 * x 2 * x 2, x 2 * x 2 * x 3, x 2 * x 3 * x 3, x 3 * x 3 * x 3]

/-- A cubic form given by its twenty usual monomial coefficients. -/
def coordinateCubic (c : Vec R 20) (x : Vec R 4) : R := c ⬝ᵥ cubicMonomials x

private def cubicReductionMatrixRow_0 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, a 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]

private def cubicReductionMatrixRow_1 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, a 1, a 0, 0, 0, a 0, 0, 0, 0, 0, 1, 0, 0, 0]

private def cubicReductionMatrixRow_2 (a : Vec R 5) : Vec R 25 :=
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, a 2, 0, a 0, 0, a 1, 0, 0, 0, 0, 0, 1, 0, 0]

private def cubicReductionMatrixRow_3 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, a 3, 0, 0, a 0, a 2, 0, 0, 0, 0, 0, 0, 1, 0]

private def cubicReductionMatrixRow_4 (a : Vec R 5) : Vec R 25 :=
  ![-(1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, a 1, 0, 0, 0, a 0, 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_5 (a : Vec R 5) : Vec R 25 :=
  ![0, 1, 0, 0, -(1), 0, 0, 0, 0, 0, 0, 0, 0, a 2, a 1, 0, 0, a 1, a 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_6 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, a 4, a 3, 0, a 1, a 3, a 2, 0, a 0, 0, 0, 0, 0, 1]

private def cubicReductionMatrixRow_7 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 1, 0, 0, 0, 0, 0, -(1), 0, 0, 0, 0, 0, a 2, 0, 0, 0, a 1, 0, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_8 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, a 3, a 2, a 4, 0, a 2, a 1, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_9 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, a 3, 1, 0, 0, a 2, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_10 (a : Vec R 5) : Vec R 25 :=
  ![0, -(1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_11 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, -(1), 0, 0, -(1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_12 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, -(1), 0, 0, 0, 0, 0, 1, 0, 0, 0, a 4, 0, 0, 0, a 3, 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_13 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 0, 0, 0, -(1), 0, 0, -(1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_14 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 0, 0, 0, 0, -(1), 0, 0, 1, 0, 0, 1, a 4, 0, 0, a 4, a 3, 0, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_15 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, a 4, 0, 1, 0, a 3, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_16 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -(1), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_17 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -(1), 0, 0, 1, 0, 0, 0, a 4, 0, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_18 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, a 4, 0, 0, 0, 0, 0]

private def cubicReductionMatrixRow_19 (a : Vec R 5) : Vec R 25 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]

def cubicReductionMatrix (a : Vec R 5) : Matrix (Fin 20) (Fin 25) R := fun i =>
  match i.val with
  | 0 => cubicReductionMatrixRow_0 a
  | 1 => cubicReductionMatrixRow_1 a
  | 2 => cubicReductionMatrixRow_2 a
  | 3 => cubicReductionMatrixRow_3 a
  | 4 => cubicReductionMatrixRow_4 a
  | 5 => cubicReductionMatrixRow_5 a
  | 6 => cubicReductionMatrixRow_6 a
  | 7 => cubicReductionMatrixRow_7 a
  | 8 => cubicReductionMatrixRow_8 a
  | 9 => cubicReductionMatrixRow_9 a
  | 10 => cubicReductionMatrixRow_10 a
  | 11 => cubicReductionMatrixRow_11 a
  | 12 => cubicReductionMatrixRow_12 a
  | 13 => cubicReductionMatrixRow_13 a
  | 14 => cubicReductionMatrixRow_14 a
  | 15 => cubicReductionMatrixRow_15 a
  | 16 => cubicReductionMatrixRow_16 a
  | 17 => cubicReductionMatrixRow_17 a
  | 18 => cubicReductionMatrixRow_18 a
  | 19 => cubicReductionMatrixRow_19 a
  | _ => 0

private def cubicReductionInverseRow_0 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, -(1), 0, 0, 0, 0, a 1, 0, 0, 0, 0, a 1, -(a 1 * a 4), a 1, -(a 1 * a 4), -(a 1 * a 3) + a 1 * a 4 * a 4, -(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)]

private def cubicReductionInverseRow_1 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -(1), 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionInverseRow_2 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -(a 2), 0, -(a 2), a 2 * a 4, a 2 * a 3 + -(a 2 * a 4 * a 4)]

private def cubicReductionInverseRow_3 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, a 4, 0, 0, -(1), 0, a 4, -(a 4 * a 4), a 4, -(a 4 * a 4), -(a 3 * a 4) + a 4 * a 4 * a 4, -(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)]

private def cubicReductionInverseRow_4 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, -(1), 0, 0, 0, a 2, -(1), 0, 0, 0, a 2, a 1 + -(a 2 * a 4), a 2, a 1 + -(a 2 * a 4), -(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4, -(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)]

private def cubicReductionInverseRow_5 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, -(1), 0, 0, 0, -(1), 0, 0, 0, a 2, 0, a 2, -(a 2 * a 4), -(a 2 * a 3) + a 2 * a 4 * a 4]

private def cubicReductionInverseRow_6 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -(1), 0, 0, 0, 0, 0, 0]

private def cubicReductionInverseRow_7 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -(a 3), -(a 2) + a 3 * a 4]

private def cubicReductionInverseRow_8 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionInverseRow_9 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionInverseRow_10 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -(1), 0, 0, 0]

private def cubicReductionInverseRow_11 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -(a 4), -(a 3) + a 4 * a 4]

private def cubicReductionInverseRow_12 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, -(a 4), 0, 0, 1, 1, -(a 4), -(a 3) + a 4 * a 4, -(a 4), -(a 3) + a 4 * a 4, -(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4), -(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4]

private def cubicReductionInverseRow_13 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, -(a 4), 1, -(a 4), -(a 3) + a 4 * a 4, -(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)]

private def cubicReductionInverseRow_14 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, -(a 4), -(a 3) + a 4 * a 4]

private def cubicReductionInverseRow_15 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -(a 4)]

private def cubicReductionInverseRow_16 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionInverseRow_17 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionInverseRow_18 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def cubicReductionInverseRow_19 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

private def cubicReductionInverseRow_20 (a : Vec R 5) : Vec R 20 :=
  ![1, 0, 0, 0, 0, 0, 0, 0, -(a 0), a 0 * a 4, 0, 0, -(a 0), -(a 0), a 0 * a 4, a 0 * a 3 + -(a 0 * a 4 * a 4), a 0 * a 4, a 0 * a 3 + -(a 0 * a 4 * a 4), a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4, a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)]

private def cubicReductionInverseRow_21 (a : Vec R 5) : Vec R 20 :=
  ![0, 1, 0, 0, 0, 0, 0, 0, -(a 1), -(a 0) + a 1 * a 4, 0, 0, -(a 1), -(a 1), -(a 0) + a 1 * a 4, a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4), -(a 0) + a 1 * a 4, a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4), a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4, a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)]

private def cubicReductionInverseRow_22 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 1, 0, 1, 0, 0, 0, -(a 2), -(a 1) + a 2 * a 4, 0, 0, -(a 2), -(a 2), -(a 1) + a 2 * a 4, -(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4), -(a 1) + a 2 * a 4, -(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4), a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4, a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)]

private def cubicReductionInverseRow_23 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 1, 0, 1, 0, 0, -(a 3), -(a 2) + a 3 * a 4, 1, 0, -(a 3), -(a 3), -(a 2) + a 3 * a 4, -(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4), -(a 2) + a 3 * a 4, -(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4), -(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4, a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)]

private def cubicReductionInverseRow_24 (a : Vec R 5) : Vec R 20 :=
  ![0, 0, 0, 0, 0, 0, 1, 1, -(a 4), -(a 3) + a 4 * a 4, 0, 1, -(a 4), -(a 4), -(a 3) + a 4 * a 4, -(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4), -(a 3) + a 4 * a 4, -(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4), -(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4, -(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)]

def cubicReductionInverse (a : Vec R 5) : Matrix (Fin 25) (Fin 20) R := fun i =>
  match i.val with
  | 0 => cubicReductionInverseRow_0 a
  | 1 => cubicReductionInverseRow_1 a
  | 2 => cubicReductionInverseRow_2 a
  | 3 => cubicReductionInverseRow_3 a
  | 4 => cubicReductionInverseRow_4 a
  | 5 => cubicReductionInverseRow_5 a
  | 6 => cubicReductionInverseRow_6 a
  | 7 => cubicReductionInverseRow_7 a
  | 8 => cubicReductionInverseRow_8 a
  | 9 => cubicReductionInverseRow_9 a
  | 10 => cubicReductionInverseRow_10 a
  | 11 => cubicReductionInverseRow_11 a
  | 12 => cubicReductionInverseRow_12 a
  | 13 => cubicReductionInverseRow_13 a
  | 14 => cubicReductionInverseRow_14 a
  | 15 => cubicReductionInverseRow_15 a
  | 16 => cubicReductionInverseRow_16 a
  | 17 => cubicReductionInverseRow_17 a
  | 18 => cubicReductionInverseRow_18 a
  | 19 => cubicReductionInverseRow_19 a
  | 20 => cubicReductionInverseRow_20 a
  | 21 => cubicReductionInverseRow_21 a
  | 22 => cubicReductionInverseRow_22 a
  | 23 => cubicReductionInverseRow_23 a
  | 24 => cubicReductionInverseRow_24 a
  | _ => 0

private theorem cubicReduction_entry_0_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 0 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_0_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((a 0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((a 0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_0_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((a 0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 1 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_1_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (1) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((1) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (-(a 4)) + ((a 0) * (1) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((1) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (1) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((1) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (1) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((1) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (-(a 4)) + ((a 0) * (1) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((1) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 1) * (-(a 3) + a 4 * a 4) + ((a 0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((1) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((a 1) * (-(a 4)) + ((a 0) * (1) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((1) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (-(a 3) + a 4 * a 4) + ((a 0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((1) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((a 1) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((a 0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((1) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_1_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((a 1) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((a 0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((1) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 2 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_2_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (1) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((1) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (-(a 4)) + ((0) * (1) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((1) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (1) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((1) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (1) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((1) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (-(a 4)) + ((0) * (1) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((1) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 2) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((a 0) * (1) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((1) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((a 2) * (-(a 4)) + ((0) * (1) + ((a 0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((1) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((a 0) * (1) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((1) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((a 2) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((a 0) * (-(a 4)) + ((0) * (1) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((1) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_2_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((a 2) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((a 0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((1) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 3 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_3_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (1) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((1) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((1) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((1) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((1) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (1) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((1) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (1) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((1) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((1) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((1) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((1) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 3) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((1) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((1) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((a 3) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((1) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((1) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((a 0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((1) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((1) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((a 3) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((a 0) * (1) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((1) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_3_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((1) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((a 3) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((a 0) * (-(a 4)) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((1) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 4 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_4_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((a 1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((a 1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((a 1) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (-(a 4)) + ((a 1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((a 1) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((a 1) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_4_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (-(1)) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((a 1) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 5 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_5_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((1) * (0) + ((0) * (0) + ((0) * (a 4) + ((-(1)) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((a 2) * (1) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((1) * (-(1)) + ((0) * (0) + ((0) * (0) + ((-(1)) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-(1)) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((1) * (0) + ((0) * (0) + ((0) * (a 4) + ((-(1)) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((a 2) * (1) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((1) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((-(1)) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((a 2) * (-(a 4)) + ((a 1) * (1) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((1) * (0) + ((0) * (0) + ((0) * (a 4) + ((-(1)) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (-(a 4)) + ((a 2) * (1) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((1) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((-(1)) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((a 2) * (-(a 4)) + ((a 1) * (1) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((1) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((-(1)) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((a 2) * (-(a 3) + a 4 * a 4) + ((a 1) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_5_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((1) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((-(1)) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((a 2) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((a 1) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (0) + ((a 1) * (0) + ((a 0) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 6 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_6_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (-(1)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (1) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((1) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (-(a 4)) + ((a 3) * (1) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((1) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(1)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (1) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((1) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(1)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (1) + ((a 3) * (0) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((1) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (-(a 4)) + ((a 3) * (1) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((1) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((1) * (a 2) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 4) * (-(a 3) + a 4 * a 4) + ((a 3) * (-(a 4)) + ((0) * (1) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((1) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((a 4) * (-(a 4)) + ((a 3) * (1) + ((0) * (0) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((1) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((1) * (a 2) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (-(a 3) + a 4 * a 4) + ((a 3) * (-(a 4)) + ((0) * (1) + ((a 1) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((1) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((1) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((a 4) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((a 3) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((a 1) * (1) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((1) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_6_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((1) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((a 4) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((a 3) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((a 1) * (-(a 4)) + ((a 3) * (0) + ((a 2) * (0) + ((0) * (0) + ((a 0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((1) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 7 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_7_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((1) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((1) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((1) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((1) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((a 2) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((1) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((1) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((a 2) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((1) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((a 2) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_7_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((1) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((a 2) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (0) + ((0) * (0) + ((a 1) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(1)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (-(1)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 8 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_8_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((1) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(a 4)) + ((0) * (1) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((1) * (0) + ((0) * (-(1)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-(1)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(1)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((1) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(a 4)) + ((0) * (1) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((1) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((a 3) * (1) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((1) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((1) * (-(a 4)) + ((0) * (1) + ((a 3) * (0) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((1) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((a 3) * (1) + ((a 2) * (0) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((1) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((1) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((1) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((a 3) * (-(a 4)) + ((a 2) * (1) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_8_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((1) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((1) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((1) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((a 3) * (-(a 3) + a 4 * a 4) + ((a 2) * (-(a 4)) + ((a 4) * (0) + ((0) * (0) + ((a 2) * (0) + ((a 1) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 9 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_9_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((a 3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((1) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((a 3) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_9_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((1) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((a 3) * (-(a 4)) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((a 2) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((-(1)) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((-(1)) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 10 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((-(1)) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_10_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((-(1)) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((-(1)) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((-(1)) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((-(1)) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((-(1)) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_10_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((-(1)) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-(1)) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((-(1)) * (1) + ((0) * (0) + ((0) * (0) + ((-(1)) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((-(1)) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((-(1)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-(1)) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 11 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_11_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-(1)) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((-(1)) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((-(1)) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((-(1)) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((-(1)) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((-(1)) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((-(1)) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((-(1)) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((-(1)) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_11_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((-(1)) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((-(1)) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((-(1)) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((a 4) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 12 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_12_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((-(1)) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((a 4) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((-(1)) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((a 4) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((-(1)) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (-(a 4)) + ((a 4) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((-(1)) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((a 4) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((-(1)) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((a 4) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_12_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((-(1)) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((a 4) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((-(1)) * (0) + ((0) * (1) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 13 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (-(1)) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_13_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((-(1)) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_13_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((-(1)) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((-(1)) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((1) * (1) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 14 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((1) * (1) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_14_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((1) * (-(a 4)) + ((a 4) * (1) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(1)) + ((0) * (0) + ((0) * (-(a 4)) + ((1) * (1) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((1) * (-(a 4)) + ((a 4) * (1) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((-(1)) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((1) * (-(a 3) + a 4 * a 4) + ((a 4) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_14_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((-(1)) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((1) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((a 4) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (0) + ((a 4) * (0) + ((a 3) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 15 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_15_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((1) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((a 4) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((a 4) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_15_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((a 4) * (-(a 4)) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((a 3) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 16 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (-(1)) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_16_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_16_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((-(1)) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 17 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_17_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((1) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_17_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((-(1)) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((1) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (0) + ((0) * (0) + ((a 4) * (0) + ((0) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_18_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 18 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((1) * (1) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_entry_18_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 19 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((1) * (-(a 4)) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((a 4) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 0 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 1 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 2 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 3 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 4 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 5 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 6 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 7 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 8 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 9 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 10 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 11 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 12 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 13 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (-(a 0)) + ((0) * (-(a 1)) + ((0) * (-(a 2)) + ((0) * (-(a 3)) + ((0) * (-(a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 14 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 15 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 16 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (a 1) + ((0) * (0) + ((0) * (0) + ((0) * (a 4) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(1)) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (a 0 * a 4) + ((0) * (-(a 0) + a 1 * a 4) + ((0) * (-(a 1) + a 2 * a 4) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (-(a 3) + a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 17 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 4)) + ((0) * (0) + ((0) * (-(a 2)) + ((0) * (-(a 4 * a 4)) + ((0) * (a 1 + -(a 2 * a 4)) + ((0) * (a 2) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4)) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4)) + ((0) * (-(a 0) + a 1 * a 4 + a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 1) + a 2 * a 4 + a 3 * a 3 + -(a 3 * a 4 * a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 18 = 0 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 3) + a 1 * a 4 * a 4) + ((0) * (0) + ((0) * (a 2 * a 4) + ((0) * (-(a 3 * a 4) + a 4 * a 4 * a 4) + ((0) * (-(a 1 * a 4) + -(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (-(a 2 * a 4)) + ((0) * (0) + ((0) * (-(a 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 4)) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (1) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (0) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + a 1 * a 2 + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4) + ((0) * (a 0 * a 4 + a 1 * a 3 + -(a 1 * a 4 * a 4) + a 2 * a 2 + -2 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4) + ((0) * (-(a 0) + a 1 * a 4 + 2 * (a 2 * a 3) + -(a 2 * a 4 * a 4) + -2 * (a 3 * a 3 * a 4) + a 3 * a 4 * a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4))))))))))))))))))))))))) = 0
  ring

private theorem cubicReduction_entry_19_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 19 = 1 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (-(a 1 * a 2) + 2 * (a 1 * a 3 * a 4) + -(a 1 * a 4 * a 4 * a 4)) + ((0) * (0) + ((0) * (a 2 * a 3 + -(a 2 * a 4 * a 4)) + ((0) * (-(a 2 * a 4) + 2 * (a 3 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 1 * a 3) + a 1 * a 4 * a 4 + -(a 2 * a 2) + 2 * (a 2 * a 3 * a 4) + -(a 2 * a 4 * a 4 * a 4)) + ((0) * (-(a 2 * a 3) + a 2 * a 4 * a 4) + ((0) * (0) + ((0) * (-(a 2) + a 3 * a 4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 1) + 2 * (a 2 * a 4) + a 3 * a 3 + -3 * (a 3 * a 4 * a 4) + a 4 * a 4 * a 4 * a 4) + ((0) * (-(a 2) + 2 * (a 3 * a 4) + -(a 4 * a 4 * a 4)) + ((0) * (-(a 3) + a 4 * a 4) + ((0) * (-(a 4)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((1) * (1) + ((0) * (a 0 * a 1 + -2 * (a 0 * a 2 * a 4) + -(a 0 * a 3 * a 3) + 3 * (a 0 * a 3 * a 4 * a 4) + -(a 0 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 2 + -2 * (a 0 * a 3 * a 4) + a 0 * a 4 * a 4 * a 4 + a 1 * a 1 + -2 * (a 1 * a 2 * a 4) + -(a 1 * a 3 * a 3) + 3 * (a 1 * a 3 * a 4 * a 4) + -(a 1 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 3 + -(a 0 * a 4 * a 4) + 2 * (a 1 * a 2) + -2 * (a 1 * a 3 * a 4) + a 1 * a 4 * a 4 * a 4 + -2 * (a 2 * a 2 * a 4) + -(a 2 * a 3 * a 3) + 3 * (a 2 * a 3 * a 4 * a 4) + -(a 2 * a 4 * a 4 * a 4 * a 4)) + ((0) * (a 0 * a 4 + 2 * (a 1 * a 3) + -(a 1 * a 4 * a 4) + a 2 * a 2 + -4 * (a 2 * a 3 * a 4) + a 2 * a 4 * a 4 * a 4 + -(a 3 * a 3 * a 3) + 3 * (a 3 * a 3 * a 4 * a 4) + -(a 3 * a 4 * a 4 * a 4 * a 4)) + ((0) * (-(a 0) + 2 * (a 1 * a 4) + 2 * (a 2 * a 3) + -3 * (a 2 * a 4 * a 4) + -3 * (a 3 * a 3 * a 4) + 4 * (a 3 * a 4 * a 4 * a 4) + -(a 4 * a 4 * a 4 * a 4 * a 4)))))))))))))))))))))))))) = 1
  ring

private theorem cubicReduction_row_0 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 0 = (1 : Mat R 20) 0 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_0_19 a

private theorem cubicReduction_row_1 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 1 = (1 : Mat R 20) 1 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_1_19 a

private theorem cubicReduction_row_2 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 2 = (1 : Mat R 20) 2 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_2_19 a

private theorem cubicReduction_row_3 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 3 = (1 : Mat R 20) 3 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_3_19 a

private theorem cubicReduction_row_4 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 4 = (1 : Mat R 20) 4 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_4_19 a

private theorem cubicReduction_row_5 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 5 = (1 : Mat R 20) 5 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_5_19 a

private theorem cubicReduction_row_6 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 6 = (1 : Mat R 20) 6 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_6_19 a

private theorem cubicReduction_row_7 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 7 = (1 : Mat R 20) 7 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_7_19 a

private theorem cubicReduction_row_8 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 8 = (1 : Mat R 20) 8 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_8_19 a

private theorem cubicReduction_row_9 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 9 = (1 : Mat R 20) 9 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_9_19 a

private theorem cubicReduction_row_10 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 10 = (1 : Mat R 20) 10 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_10_19 a

private theorem cubicReduction_row_11 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 11 = (1 : Mat R 20) 11 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_11_19 a

private theorem cubicReduction_row_12 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 12 = (1 : Mat R 20) 12 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_12_19 a

private theorem cubicReduction_row_13 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 13 = (1 : Mat R 20) 13 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_13_19 a

private theorem cubicReduction_row_14 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 14 = (1 : Mat R 20) 14 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_14_19 a

private theorem cubicReduction_row_15 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 15 = (1 : Mat R 20) 15 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_15_19 a

private theorem cubicReduction_row_16 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 16 = (1 : Mat R 20) 16 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_16_19 a

private theorem cubicReduction_row_17 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 17 = (1 : Mat R 20) 17 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_17_19 a

private theorem cubicReduction_row_18 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 18 = (1 : Mat R 20) 18 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_18_19 a

private theorem cubicReduction_row_19 (a : Vec R 5) :
    (cubicReductionMatrix a * cubicReductionInverse a) 19 = (1 : Mat R 20) 19 := by
  funext j
  fin_cases j
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_0 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_1 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_2 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_3 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_4 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_5 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_6 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_7 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_8 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_9 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_10 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_11 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_12 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_13 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_14 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_15 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_16 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_17 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_18 a
  · simpa [Matrix.one_apply] using cubicReduction_entry_19_19 a

theorem cubicReduction_rightInverse (a : Vec R 5) :
    cubicReductionMatrix a * cubicReductionInverse a = 1 := by
  funext i
  fin_cases i
  · exact cubicReduction_row_0 a
  · exact cubicReduction_row_1 a
  · exact cubicReduction_row_2 a
  · exact cubicReduction_row_3 a
  · exact cubicReduction_row_4 a
  · exact cubicReduction_row_5 a
  · exact cubicReduction_row_6 a
  · exact cubicReduction_row_7 a
  · exact cubicReduction_row_8 a
  · exact cubicReduction_row_9 a
  · exact cubicReduction_row_10 a
  · exact cubicReduction_row_11 a
  · exact cubicReduction_row_12 a
  · exact cubicReduction_row_13 a
  · exact cubicReduction_row_14 a
  · exact cubicReduction_row_15 a
  · exact cubicReduction_row_16 a
  · exact cubicReduction_row_17 a
  · exact cubicReduction_row_18 a
  · exact cubicReduction_row_19 a

/-- Coefficients of the quadratic multiples and the residual five monomials. -/
def cubicReduction (a : Vec R 5) (c : Vec R 20) : Vec R 25 := (cubicReductionInverse a).mulVec c

theorem cubicReduction_reconstruct (a : Vec R 5) (c : Vec R 20) :
    (cubicReductionMatrix a).mulVec (cubicReduction a c) = c := by
  rw [cubicReduction, Matrix.mulVec_mulVec, cubicReduction_rightInverse, Matrix.one_mulVec]

end
end PfaffianDescent
