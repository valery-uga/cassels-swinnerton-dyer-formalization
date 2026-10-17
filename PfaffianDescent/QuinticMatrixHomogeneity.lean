import PfaffianDescent.QuinticCoordinateReduction

namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
section
variable {K : Type*} [Field K]

lemma quinticPolynomialMatrix_homogeneous (a : Vec K 5) (i j : Fin 5) :
    (quinticPolynomialMatrix a i j).IsHomogeneous 1 := by
  have hx (k : Fin 4) := isHomogeneous_X K k
  have hc (k : Fin 5) (j : Fin 4) := isHomogeneous_C_mul_X (a k) j
  have hz : (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1 :=
    (homogeneousSubmodule (Fin 4) K 1).zero_mem
  fin_cases i <;> fin_cases j
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact hz
  · change (C (a 3) * X 3 + C (a 0) * X 0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (hc 3 3).add (hc 0 0)
  · change (C (a 4) * X 3 + C (a 1) * X 0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (hc 4 3).add (hc 1 0)
  · change (-X 3 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (hx 3).neg
  · change (X 2 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact hx 2
  · change (-(C (a 3) * X 3 + C (a 0) * X 0) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact ((hc 3 3).add (hc 0 0)).neg
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact hz
  · change (X 3 + C (a 2) * X 0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (hx 3).add (hc 2 0)
  · change (X 2 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact hx 2
  · change (-X 1 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (hx 1).neg
  · change (-(C (a 4) * X 3 + C (a 1) * X 0) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact ((hc 4 3).add (hc 1 0)).neg
  · change (-(X 3 + C (a 2) * X 0) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact ((hx 3).add (hc 2 0)).neg
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact hz
  · change (-X 1 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (hx 1).neg
  · change (X 0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact hx 0
  · change (-(-X 3) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (hx 3).neg.neg
  · change (-(X 2) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (hx 2).neg
  · change (-(-X 1) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (hx 1).neg.neg
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact hz
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact hz
  · change (-(X 2) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (hx 2).neg
  · change (-(-X 1) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (hx 1).neg.neg
  · change (-(X 0) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact (hx 0).neg
  · change (-(0) : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact hz.neg
  · change (0 : MvPolynomial (Fin 4) K).IsHomogeneous 1
    exact hz

lemma quinticPolynomialMatrix_component (a : Vec K 5) (d : ℕ)
    (v : Fin 5 → MvPolynomial (Fin 4) K) (i : Fin 5) :
    (quinticPolynomialMatrix a).mulVec (fun j => homogeneousComponent d (v j)) i =
      homogeneousComponent (d + 1) ((quinticPolynomialMatrix a).mulVec v i) := by
  change (∑ j, quinticPolynomialMatrix a i j * homogeneousComponent d (v j)) =
    homogeneousComponent (d + 1) (∑ j, quinticPolynomialMatrix a i j * v j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simpa only [Nat.add_comm 1 d] using
    (homogeneousComponent_mul_left (quinticPolynomialMatrix_homogeneous a i j) d).symm

end
end PfaffianDescent
