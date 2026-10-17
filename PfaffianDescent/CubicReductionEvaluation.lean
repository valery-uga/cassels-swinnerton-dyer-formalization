import PfaffianDescent.CubicReduction

namespace PfaffianDescent
section
variable {R S : Type*} [CommRing R] [CommRing S]

def cubicReductionValues (a : Vec R 5) (x : Vec R 4) : Vec R 25 :=
  ![x 0 * quinticQuadrics a x 0, x 1 * quinticQuadrics a x 0, x 2 * quinticQuadrics a x 0, x 3 * quinticQuadrics a x 0, x 0 * quinticQuadrics a x 1, x 1 * quinticQuadrics a x 1, x 2 * quinticQuadrics a x 1, x 3 * quinticQuadrics a x 1, x 0 * quinticQuadrics a x 2, x 1 * quinticQuadrics a x 2, x 2 * quinticQuadrics a x 2, x 3 * quinticQuadrics a x 2, x 0 * quinticQuadrics a x 3, x 1 * quinticQuadrics a x 3, x 2 * quinticQuadrics a x 3, x 3 * quinticQuadrics a x 3, x 0 * quinticQuadrics a x 4, x 1 * quinticQuadrics a x 4, x 2 * quinticQuadrics a x 4, x 3 * quinticQuadrics a x 4, x 0 * x 0 * x 0, x 0 * x 0 * x 1, x 0 * x 0 * x 2, x 0 * x 0 * x 3, x 0 * x 1 * x 3]

private theorem cubicReduction_value_0 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 0 = cubicReductionValues a x 0 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((1) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((-(1)) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 0 * (x 0 * x 2 - x 1^2)
  ring

private theorem cubicReduction_value_1 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 1 = cubicReductionValues a x 1 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((1) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((-(1)) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 1 * (x 0 * x 2 - x 1^2)
  ring

private theorem cubicReduction_value_2 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 2 = cubicReductionValues a x 2 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((1) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((-(1)) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 2 * (x 0 * x 2 - x 1^2)
  ring

private theorem cubicReduction_value_3 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 3 = cubicReductionValues a x 3 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((1) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((-(1)) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 3 * (x 0 * x 2 - x 1^2)
  ring

private theorem cubicReduction_value_4 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 4 = cubicReductionValues a x 4 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((1) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((-(1)) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 0 * (x 0 * x 3 - x 1 * x 2)
  ring

private theorem cubicReduction_value_5 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 5 = cubicReductionValues a x 5 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((1) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((-(1)) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 1 * (x 0 * x 3 - x 1 * x 2)
  ring

private theorem cubicReduction_value_6 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 6 = cubicReductionValues a x 6 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((1) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((-(1)) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 2 * (x 0 * x 3 - x 1 * x 2)
  ring

private theorem cubicReduction_value_7 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 7 = cubicReductionValues a x 7 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((1) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((-(1)) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 3 * (x 0 * x 3 - x 1 * x 2)
  ring

private theorem cubicReduction_value_8 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 8 = cubicReductionValues a x 8 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((1) * (x 0 * x 1 * x 3) + ((-(1)) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 0 * (x 1 * x 3 - x 2^2)
  ring

private theorem cubicReduction_value_9 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 9 = cubicReductionValues a x 9 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((1) * (x 1 * x 1 * x 3) + ((-(1)) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 1 * (x 1 * x 3 - x 2^2)
  ring

private theorem cubicReduction_value_10 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 10 = cubicReductionValues a x 10 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((1) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((-(1)) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 2 * (x 1 * x 3 - x 2^2)
  ring

private theorem cubicReduction_value_11 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 11 = cubicReductionValues a x 11 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((1) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((-(1)) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 3 * (x 1 * x 3 - x 2^2)
  ring

private theorem cubicReduction_value_12 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 12 = cubicReductionValues a x 12 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (a 0) * (x 0 * x 0 * x 0) + ((a 1) * (x 0 * x 0 * x 1) + ((a 2) * (x 0 * x 0 * x 2) + ((a 3) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((a 4) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((1) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 0 * (x 2 * x 3 + a 4 * x 1 * x 3 + a 3 * x 0 * x 3 + a 2 * x 0 * x 2 + a 1 * x 0 * x 1 + a 0 * x 0^2)
  ring

private theorem cubicReduction_value_13 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 13 = cubicReductionValues a x 13 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((a 0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((a 1) * (x 0 * x 1 * x 1) + ((a 2) * (x 0 * x 1 * x 2) + ((a 3) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((a 4) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((1) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 1 * (x 2 * x 3 + a 4 * x 1 * x 3 + a 3 * x 0 * x 3 + a 2 * x 0 * x 2 + a 1 * x 0 * x 1 + a 0 * x 0^2)
  ring

private theorem cubicReduction_value_14 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 14 = cubicReductionValues a x 14 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((a 0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((a 1) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((a 2) * (x 0 * x 2 * x 2) + ((a 3) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((a 4) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((1) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 2 * (x 2 * x 3 + a 4 * x 1 * x 3 + a 3 * x 0 * x 3 + a 2 * x 0 * x 2 + a 1 * x 0 * x 1 + a 0 * x 0^2)
  ring

private theorem cubicReduction_value_15 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 15 = cubicReductionValues a x 15 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((a 0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((a 1) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((a 2) * (x 0 * x 2 * x 3) + ((a 3) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((a 4) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((1) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 3 * (x 2 * x 3 + a 4 * x 1 * x 3 + a 3 * x 0 * x 3 + a 2 * x 0 * x 2 + a 1 * x 0 * x 1 + a 0 * x 0^2)
  ring

private theorem cubicReduction_value_16 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 16 = cubicReductionValues a x 16 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((a 0) * (x 0 * x 0 * x 1) + ((a 1) * (x 0 * x 0 * x 2) + ((a 2) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((a 3) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((a 4) * (x 0 * x 2 * x 3) + ((1) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 0 * (x 3^2 + a 4 * x 2 * x 3 + a 3 * x 1 * x 3 + a 2 * x 0 * x 3 + a 1 * x 0 * x 2 + a 0 * x 0 * x 1)
  ring

private theorem cubicReduction_value_17 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 17 = cubicReductionValues a x 17 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((a 0) * (x 0 * x 1 * x 1) + ((a 1) * (x 0 * x 1 * x 2) + ((a 2) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((a 3) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((a 4) * (x 1 * x 2 * x 3) + ((1) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 1 * (x 3^2 + a 4 * x 2 * x 3 + a 3 * x 1 * x 3 + a 2 * x 0 * x 3 + a 1 * x 0 * x 2 + a 0 * x 0 * x 1)
  ring

private theorem cubicReduction_value_18 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 18 = cubicReductionValues a x 18 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((a 0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((a 1) * (x 0 * x 2 * x 2) + ((a 2) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((a 3) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((a 4) * (x 2 * x 2 * x 3) + ((1) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 2 * (x 3^2 + a 4 * x 2 * x 3 + a 3 * x 1 * x 3 + a 2 * x 0 * x 3 + a 1 * x 0 * x 2 + a 0 * x 0 * x 1)
  ring

private theorem cubicReduction_value_19 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 19 = cubicReductionValues a x 19 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((a 0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((a 1) * (x 0 * x 2 * x 3) + ((a 2) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((a 3) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((a 4) * (x 2 * x 3 * x 3) + ((1) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 3 * (x 3^2 + a 4 * x 2 * x 3 + a 3 * x 1 * x 3 + a 2 * x 0 * x 3 + a 1 * x 0 * x 2 + a 0 * x 0 * x 1)
  ring

private theorem cubicReduction_value_20 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 20 = cubicReductionValues a x 20 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (1) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 0 * x 0 * x 0
  ring

private theorem cubicReduction_value_21 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 21 = cubicReductionValues a x 21 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((1) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 0 * x 0 * x 1
  ring

private theorem cubicReduction_value_22 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 22 = cubicReductionValues a x 22 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((1) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 0 * x 0 * x 2
  ring

private theorem cubicReduction_value_23 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 23 = cubicReductionValues a x 23 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((1) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((0) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 0 * x 0 * x 3
  ring

private theorem cubicReduction_value_24 (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) 24 = cubicReductionValues a x 24 := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (0) * (x 0 * x 0 * x 0) + ((0) * (x 0 * x 0 * x 1) + ((0) * (x 0 * x 0 * x 2) + ((0) * (x 0 * x 0 * x 3) + ((0) * (x 0 * x 1 * x 1) + ((0) * (x 0 * x 1 * x 2) + ((1) * (x 0 * x 1 * x 3) + ((0) * (x 0 * x 2 * x 2) + ((0) * (x 0 * x 2 * x 3) + ((0) * (x 0 * x 3 * x 3) + ((0) * (x 1 * x 1 * x 1) + ((0) * (x 1 * x 1 * x 2) + ((0) * (x 1 * x 1 * x 3) + ((0) * (x 1 * x 2 * x 2) + ((0) * (x 1 * x 2 * x 3) + ((0) * (x 1 * x 3 * x 3) + ((0) * (x 2 * x 2 * x 2) + ((0) * (x 2 * x 2 * x 3) + ((0) * (x 2 * x 3 * x 3) + ((0) * (x 3 * x 3 * x 3)))))))))))))))))))) = x 0 * x 1 * x 3
  ring

theorem cubicReduction_values (a : Vec R 5) (x : Vec R 4) :
    (cubicReductionMatrix a).transpose.mulVec (cubicMonomials x) = cubicReductionValues a x := by
  funext i
  fin_cases i
  · exact cubicReduction_value_0 a x
  · exact cubicReduction_value_1 a x
  · exact cubicReduction_value_2 a x
  · exact cubicReduction_value_3 a x
  · exact cubicReduction_value_4 a x
  · exact cubicReduction_value_5 a x
  · exact cubicReduction_value_6 a x
  · exact cubicReduction_value_7 a x
  · exact cubicReduction_value_8 a x
  · exact cubicReduction_value_9 a x
  · exact cubicReduction_value_10 a x
  · exact cubicReduction_value_11 a x
  · exact cubicReduction_value_12 a x
  · exact cubicReduction_value_13 a x
  · exact cubicReduction_value_14 a x
  · exact cubicReduction_value_15 a x
  · exact cubicReduction_value_16 a x
  · exact cubicReduction_value_17 a x
  · exact cubicReduction_value_18 a x
  · exact cubicReduction_value_19 a x
  · exact cubicReduction_value_20 a x
  · exact cubicReduction_value_21 a x
  · exact cubicReduction_value_22 a x
  · exact cubicReduction_value_23 a x
  · exact cubicReduction_value_24 a x

theorem cubicReduction_evaluate (a : Vec R 5) (u : Vec R 25) (x : Vec R 4) :
    coordinateCubic ((cubicReductionMatrix a).mulVec u) x = u ⬝ᵥ cubicReductionValues a x := by
  rw [coordinateCubic, dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, cubicReduction_values]

private theorem cubicReduction_map_row_0 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 0 = cubicReductionMatrix (fun j => f (a j)) 0 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_1 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 1 = cubicReductionMatrix (fun j => f (a j)) 1 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_2 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 2 = cubicReductionMatrix (fun j => f (a j)) 2 := by
  funext j
  fin_cases j
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_3 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 3 = cubicReductionMatrix (fun j => f (a j)) 3 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f

private theorem cubicReduction_map_row_4 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 4 = cubicReductionMatrix (fun j => f (a j)) 4 := by
  funext j
  fin_cases j
  · exact (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_5 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 5 = cubicReductionMatrix (fun j => f (a j)) 5 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_6 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 6 = cubicReductionMatrix (fun j => f (a j)) 6 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · rfl
  · rfl
  · rfl
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f

private theorem cubicReduction_map_row_7 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 7 = cubicReductionMatrix (fun j => f (a j)) 7 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_8 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 8 = cubicReductionMatrix (fun j => f (a j)) 8 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · rfl
  · rfl
  · rfl
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_9 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 9 = cubicReductionMatrix (fun j => f (a j)) 9 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_10 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 10 = cubicReductionMatrix (fun j => f (a j)) 10 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_11 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 11 = cubicReductionMatrix (fun j => f (a j)) 11 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  · exact map_zero f
  · exact map_zero f
  · exact (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_12 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 12 = cubicReductionMatrix (fun j => f (a j)) 12 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_13 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 13 = cubicReductionMatrix (fun j => f (a j)) 13 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  · exact map_zero f
  · exact map_zero f
  · exact (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_14 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 14 = cubicReductionMatrix (fun j => f (a j)) 14 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · rfl
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_15 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 15 = cubicReductionMatrix (fun j => f (a j)) 15 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_16 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 16 = cubicReductionMatrix (fun j => f (a j)) 16 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_17 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 17 = cubicReductionMatrix (fun j => f (a j)) 17 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact (map_neg f 1).trans (congrArg Neg.neg (map_one f))
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_18 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 18 = cubicReductionMatrix (fun j => f (a j)) 18 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · rfl
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

private theorem cubicReduction_map_row_19 (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f 19 = cubicReductionMatrix (fun j => f (a j)) 19 := by
  funext j
  fin_cases j
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_one f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f
  · exact map_zero f

theorem cubicReductionMatrix_map (f : R →+* S) (a : Vec R 5) :
    (cubicReductionMatrix a).map f = cubicReductionMatrix (fun j => f (a j)) := by
  funext i
  fin_cases i
  · exact cubicReduction_map_row_0 f a
  · exact cubicReduction_map_row_1 f a
  · exact cubicReduction_map_row_2 f a
  · exact cubicReduction_map_row_3 f a
  · exact cubicReduction_map_row_4 f a
  · exact cubicReduction_map_row_5 f a
  · exact cubicReduction_map_row_6 f a
  · exact cubicReduction_map_row_7 f a
  · exact cubicReduction_map_row_8 f a
  · exact cubicReduction_map_row_9 f a
  · exact cubicReduction_map_row_10 f a
  · exact cubicReduction_map_row_11 f a
  · exact cubicReduction_map_row_12 f a
  · exact cubicReduction_map_row_13 f a
  · exact cubicReduction_map_row_14 f a
  · exact cubicReduction_map_row_15 f a
  · exact cubicReduction_map_row_16 f a
  · exact cubicReduction_map_row_17 f a
  · exact cubicReduction_map_row_18 f a
  · exact cubicReduction_map_row_19 f a

end
end PfaffianDescent
