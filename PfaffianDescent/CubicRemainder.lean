import PfaffianDescent.CubicReductionEvaluation
import Mathlib.Tactic.LinearCombination

namespace PfaffianDescent
section
variable {R : Type*} [CommRing R]

def reductionLinearForms (u : Vec R 25) : Fin 5 → Vec R 4 :=
  ![![u 0, u 1, u 2, u 3], ![u 4, u 5, u 6, u 7], ![u 8, u 9, u 10, u 11], ![u 12, u 13, u 14, u 15], ![u 16, u 17, u 18, u 19]]

def reductionRemainder (u : Vec R 25) : Vec R 5 := ![u 20, u 21, u 22, u 23, u 24]

def remainderCubic (r : Vec R 5) (x : Vec R 4) : R :=
  r 0 * x 0^3 + r 1 * x 0^2 * x 1 + r 2 * x 0^2 * x 2 +
    r 3 * x 0^2 * x 3 + r 4 * x 0 * x 1 * x 3

theorem remainderCubic_zero (x : Vec R 4) : remainderCubic 0 x = 0 := by
  simp only [remainderCubic, Pi.zero_apply, zero_mul, add_zero]

theorem cubicReduction_pairing (a : Vec R 5) (u : Vec R 25) (x : Vec R 4) :
    u ⬝ᵥ cubicReductionValues a x =
      (∑ i, linearValue (reductionLinearForms u i) x * quinticQuadrics a x i) +
        remainderCubic (reductionRemainder u) x := by
  simp only [dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change u 0 * (x 0 * quinticQuadrics a x 0) + (u 1 * (x 1 * quinticQuadrics a x 0) + (u 2 * (x 2 * quinticQuadrics a x 0) + (u 3 * (x 3 * quinticQuadrics a x 0) + (u 4 * (x 0 * quinticQuadrics a x 1) + (u 5 * (x 1 * quinticQuadrics a x 1) + (u 6 * (x 2 * quinticQuadrics a x 1) + (u 7 * (x 3 * quinticQuadrics a x 1) + (u 8 * (x 0 * quinticQuadrics a x 2) + (u 9 * (x 1 * quinticQuadrics a x 2) + (u 10 * (x 2 * quinticQuadrics a x 2) + (u 11 * (x 3 * quinticQuadrics a x 2) + (u 12 * (x 0 * quinticQuadrics a x 3) + (u 13 * (x 1 * quinticQuadrics a x 3) + (u 14 * (x 2 * quinticQuadrics a x 3) + (u 15 * (x 3 * quinticQuadrics a x 3) + (u 16 * (x 0 * quinticQuadrics a x 4) + (u 17 * (x 1 * quinticQuadrics a x 4) + (u 18 * (x 2 * quinticQuadrics a x 4) + (u 19 * (x 3 * quinticQuadrics a x 4) + (u 20 * (x 0 * x 0 * x 0) + (u 21 * (x 0 * x 0 * x 1) + (u 22 * (x 0 * x 0 * x 2) + (u 23 * (x 0 * x 0 * x 3) + (u 24 * (x 0 * x 1 * x 3))))))))))))))))))))))))) = ((u 0 * x 0 + u 1 * x 1 + u 2 * x 2 + u 3 * x 3) * quinticQuadrics a x 0 + ((u 4 * x 0 + u 5 * x 1 + u 6 * x 2 + u 7 * x 3) * quinticQuadrics a x 1 + ((u 8 * x 0 + u 9 * x 1 + u 10 * x 2 + u 11 * x 3) * quinticQuadrics a x 2 + ((u 12 * x 0 + u 13 * x 1 + u 14 * x 2 + u 15 * x 3) * quinticQuadrics a x 3 + ((u 16 * x 0 + u 17 * x 1 + u 18 * x 2 + u 19 * x 3) * quinticQuadrics a x 4))))) + (u 20 * x 0^3 + u 21 * x 0^2 * x 1 + u 22 * x 0^2 * x 2 + u 23 * x 0^2 * x 3 + u 24 * x 0 * x 1 * x 3)
  ring

/-- Every cubic is a sum of linear multiples of the five quadrics and a five-term remainder. -/
theorem cubic_reduction_formula (a : Vec R 5) (c : Vec R 20) (x : Vec R 4) :
    coordinateCubic c x =
      (∑ i, linearValue (reductionLinearForms (cubicReduction a c) i) x * quinticQuadrics a x i) +
        remainderCubic (reductionRemainder (cubicReduction a c)) x := by
  rw [← cubicReduction_pairing, ← cubicReduction_evaluate, cubicReduction_reconstruct]

variable {S : Type*} [CommRing S]

theorem cubic_reduction_formula_map (f : R →+* S) (a : Vec R 5) (c : Vec R 20) (x : Vec S 4) :
    coordinateCubic (fun i => f (c i)) x =
      (∑ i, linearValue (reductionLinearForms (fun j => f (cubicReduction a c j)) i) x *
        quinticQuadrics (fun j => f (a j)) x i) +
        remainderCubic (reductionRemainder (fun j => f (cubicReduction a c j))) x := by
  rw [← cubicReduction_pairing, ← cubicReduction_evaluate]
  congr 1
  funext i
  have h := congrArg (fun v : Vec R 20 => f (v i)) (cubicReduction_reconstruct a c)
  rw [f.map_mulVec, cubicReductionMatrix_map] at h
  exact h.symm

def rationalCubicCoordinates (z : R) : Vec R 4 := ![1, z, z^2, z^3]

def quinticRelation (a : Vec R 5) (z : R) : Prop :=
  z^5 + a 4 * z^4 + a 3 * z^3 + a 2 * z^2 + a 1 * z + a 0 = 0

theorem quinticQuadrics_at_root (a : Vec R 5) (z : R) (hz : quinticRelation a z) :
    quinticQuadrics a (rationalCubicCoordinates z) = 0 := by
  change z^5 + a 4 * z^4 + a 3 * z^3 + a 2 * z^2 + a 1 * z + a 0 = 0 at hz
  funext i
  fin_cases i
  · change 1 * z^2 - z^2 = 0
    ring
  · change 1 * z^3 - z * z^2 = 0
    ring
  · change z * z^3 - (z^2)^2 = 0
    ring
  · change z^2 * z^3 + a 4 * z * z^3 + a 3 * 1 * z^3 + a 2 * 1 * z^2 + a 1 * 1 * z + a 0 * 1^2 = 0
    linear_combination hz
  · change (z^3)^2 + a 4 * z^2 * z^3 + a 3 * z * z^3 + a 2 * 1 * z^3 + a 1 * 1 * z^2 + a 0 * 1 * z = 0
    linear_combination z * hz

end
end PfaffianDescent
