import PfaffianDescent.Constraints

namespace PfaffianDescent
section Ring
variable {R : Type*} [CommRing R]

def constraintForcing : Vec R 20 := Pi.single 18 (-2)

/-- A polynomial vector in the simultaneous contraction kernel. -/
def kernelVector (A : Fin 3 → Mat R 6) : Vec R 20 :=
  (constraintMatrix A).adjugate.mulVec constraintForcing

theorem constraintMatrix_kernelVector (A : Fin 3 → Mat R 6) :
    (constraintMatrix A).mulVec (kernelVector A) = (constraintMatrix A).det • constraintForcing := by
  rw [kernelVector, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem kernelVector_contraction (A : Fin 3 → Mat R 6) :
    ∀ i, contract3 (A i) (kernelVector A) = 0 := by
  intro i
  fin_cases i
  · funext j
    fin_cases j
    · change contract3 (A 0) (kernelVector A) 0 = 0
      rw [← constraintMatrix_row_0 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 0) (kernelVector A) 1 = 0
      rw [← constraintMatrix_row_1 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 0) (kernelVector A) 2 = 0
      rw [← constraintMatrix_row_2 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 0) (kernelVector A) 3 = 0
      rw [← constraintMatrix_row_3 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 0) (kernelVector A) 4 = 0
      rw [← constraintMatrix_row_4 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 0) (kernelVector A) 5 = 0
      rw [← constraintMatrix_row_5 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
  · funext j
    fin_cases j
    · change contract3 (A 1) (kernelVector A) 0 = 0
      rw [← constraintMatrix_row_6 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 1) (kernelVector A) 1 = 0
      rw [← constraintMatrix_row_7 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 1) (kernelVector A) 2 = 0
      rw [← constraintMatrix_row_8 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 1) (kernelVector A) 3 = 0
      rw [← constraintMatrix_row_9 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 1) (kernelVector A) 4 = 0
      rw [← constraintMatrix_row_10 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 1) (kernelVector A) 5 = 0
      rw [← constraintMatrix_row_11 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
  · funext j
    fin_cases j
    · change contract3 (A 2) (kernelVector A) 0 = 0
      rw [← constraintMatrix_row_12 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 2) (kernelVector A) 1 = 0
      rw [← constraintMatrix_row_13 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 2) (kernelVector A) 2 = 0
      rw [← constraintMatrix_row_14 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 2) (kernelVector A) 3 = 0
      rw [← constraintMatrix_row_15 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 2) (kernelVector A) 4 = 0
      rw [← constraintMatrix_row_16 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _
    · change contract3 (A 2) (kernelVector A) 5 = 0
      rw [← constraintMatrix_row_17 A (kernelVector A), constraintMatrix_kernelVector]
      change (constraintMatrix A).det * 0 = 0
      exact mul_zero _

variable {S : Type*} [CommRing S]

theorem constraintForcing_map (f : R →+* S) :
    f ∘ (constraintForcing : Vec R 20) = constraintForcing := by
  funext i
  by_cases h : i = 18 <;> simp [constraintForcing, h, map_ofNat]

theorem kernelVector_map (f : R →+* S) (A : Fin 3 → Mat R 6) :
    (fun i => f (kernelVector A i)) = kernelVector (fun j => (A j).map f) := by
  funext i
  have ha : ((constraintMatrix A).adjugate).map f = ((constraintMatrix A).map f).adjugate :=
    f.map_adjugate (constraintMatrix A)
  simp only [kernelVector]
  rw [f.map_mulVec, ha, constraintMatrix_map, constraintForcing_map]

theorem goodTriple_contraction : ∀ i : Fin 3, contract3 (goodTriple i) (goodTrivector : Vec R 20) = 0 := by
  intro i
  fin_cases i
  · funext j
    fin_cases j
    · change ((0) * (0) + (0) * (0) + (0) * (0) + (0) * (0) + (0) * (1) + (2) * (0) + (0) * (0) + (0) * (0) + (-1) * (0) + (0) * (1) : R) = 0
      norm_num
    · change (- (0) * (0) - (0) * (0) - (0) * (0) - (0) * (0) + (0) * (1) + (0) * (0) + (-2) * (0) + (-2) * (0) + (0) * (0) + (0) * (1) : R) = 0
      norm_num
    · change ((0) * (1) - (0) * (0) - (2) * (0) - (0) * (0) - (0) * (0) - (0) * (0) - (-2) * (0) + (0) * (0) + (0) * (0) + (0) * (1) : R) = 0
      norm_num
    · change ((0) * (1) + (0) * (0) - (0) * (0) - (-1) * (0) + (0) * (0) - (-2) * (0) - (0) * (0) - (0) * (0) - (0) * (0) + (0) * (1) : R) = 0
      norm_num
    · change ((0) * (1) + (2) * (0) + (0) * (0) - (0) * (0) + (0) * (0) + (-2) * (0) - (0) * (0) + (0) * (1) - (0) * (0) - (0) * (0) : R) = 0
      norm_num
    · change ((0) * (1) + (0) * (0) + (-1) * (0) + (0) * (0) + (-2) * (0) + (0) * (0) + (0) * (0) + (0) * (1) + (0) * (0) + (0) * (0) : R) = 0
      norm_num
  · funext j
    fin_cases j
    · change ((0) * (0) + (0) * (0) + (0) * (0) + (0) * (0) + (0) * (2) + (2) * (0) + (0) * (0) + (0) * (0) + (-1) * (0) + (0) * (3) : R) = 0
      norm_num
    · change (- (0) * (0) - (0) * (0) - (0) * (0) - (0) * (0) + (0) * (2) + (0) * (0) + (-2) * (0) + (-2) * (0) + (0) * (0) + (0) * (3) : R) = 0
      norm_num
    · change ((0) * (1) - (0) * (0) - (2) * (0) - (0) * (0) - (0) * (0) - (0) * (0) - (-2) * (0) + (0) * (0) + (0) * (0) + (0) * (3) : R) = 0
      norm_num
    · change ((0) * (1) + (0) * (0) - (0) * (0) - (-1) * (0) + (0) * (0) - (-2) * (0) - (0) * (0) - (0) * (0) - (0) * (0) + (0) * (3) : R) = 0
      norm_num
    · change ((0) * (1) + (2) * (0) + (0) * (0) - (0) * (0) + (0) * (0) + (-2) * (0) - (0) * (0) + (0) * (2) - (0) * (0) - (0) * (0) : R) = 0
      norm_num
    · change ((0) * (1) + (0) * (0) + (-1) * (0) + (0) * (0) + (-2) * (0) + (0) * (0) + (0) * (0) + (0) * (2) + (0) * (0) + (0) * (0) : R) = 0
      norm_num
  · funext j
    fin_cases j
    · change ((0) * (0) + (0) * (1) + (0) * (0) + (0) * (1) + (0) * (0) + (2) * (1) + (0) * (0) + (0) * (0) + (-1) * (2) + (0) * (0) : R) = 0
      norm_num
    · change (- (0) * (1) - (0) * (0) - (0) * (1) - (0) * (0) + (0) * (0) + (0) * (1) + (-2) * (0) + (-2) * (0) + (0) * (2) + (0) * (0) : R) = 0
      norm_num
    · change ((0) * (0) - (0) * (0) - (2) * (1) - (0) * (0) - (0) * (1) - (0) * (0) - (-2) * (1) + (0) * (0) + (0) * (2) + (0) * (0) : R) = 0
      norm_num
    · change ((0) * (0) + (0) * (1) - (0) * (1) - (-1) * (0) + (0) * (0) - (-2) * (0) - (0) * (1) - (0) * (1) - (0) * (0) + (0) * (0) : R) = 0
      norm_num
    · change ((0) * (0) + (2) * (1) + (0) * (0) - (0) * (0) + (0) * (0) + (-2) * (1) - (0) * (1) + (0) * (0) - (0) * (0) - (0) * (2) : R) = 0
      norm_num
    · change ((0) * (0) + (0) * (1) + (-1) * (0) + (0) * (1) + (-2) * (0) + (0) * (1) + (0) * (0) + (0) * (0) + (0) * (1) + (0) * (0) : R) = 0
      norm_num

theorem goodConstraint_goodTrivector :
    (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector = constraintForcing := by
  funext i
  fin_cases i
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 0 = constraintForcing 0
    rw [constraintMatrix_row_0 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 0) (goodTrivector : Vec R 20) 0 = 0
    exact congrFun (goodTriple_contraction 0) 0
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 1 = constraintForcing 1
    rw [constraintMatrix_row_1 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 0) (goodTrivector : Vec R 20) 1 = 0
    exact congrFun (goodTriple_contraction 0) 1
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 2 = constraintForcing 2
    rw [constraintMatrix_row_2 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 0) (goodTrivector : Vec R 20) 2 = 0
    exact congrFun (goodTriple_contraction 0) 2
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 3 = constraintForcing 3
    rw [constraintMatrix_row_3 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 0) (goodTrivector : Vec R 20) 3 = 0
    exact congrFun (goodTriple_contraction 0) 3
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 4 = constraintForcing 4
    rw [constraintMatrix_row_4 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 0) (goodTrivector : Vec R 20) 4 = 0
    exact congrFun (goodTriple_contraction 0) 4
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 5 = constraintForcing 5
    rw [constraintMatrix_row_5 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 0) (goodTrivector : Vec R 20) 5 = 0
    exact congrFun (goodTriple_contraction 0) 5
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 6 = constraintForcing 6
    rw [constraintMatrix_row_6 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 1) (goodTrivector : Vec R 20) 0 = 0
    exact congrFun (goodTriple_contraction 1) 0
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 7 = constraintForcing 7
    rw [constraintMatrix_row_7 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 1) (goodTrivector : Vec R 20) 1 = 0
    exact congrFun (goodTriple_contraction 1) 1
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 8 = constraintForcing 8
    rw [constraintMatrix_row_8 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 1) (goodTrivector : Vec R 20) 2 = 0
    exact congrFun (goodTriple_contraction 1) 2
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 9 = constraintForcing 9
    rw [constraintMatrix_row_9 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 1) (goodTrivector : Vec R 20) 3 = 0
    exact congrFun (goodTriple_contraction 1) 3
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 10 = constraintForcing 10
    rw [constraintMatrix_row_10 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 1) (goodTrivector : Vec R 20) 4 = 0
    exact congrFun (goodTriple_contraction 1) 4
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 11 = constraintForcing 11
    rw [constraintMatrix_row_11 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 1) (goodTrivector : Vec R 20) 5 = 0
    exact congrFun (goodTriple_contraction 1) 5
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 12 = constraintForcing 12
    rw [constraintMatrix_row_12 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 2) (goodTrivector : Vec R 20) 0 = 0
    exact congrFun (goodTriple_contraction 2) 0
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 13 = constraintForcing 13
    rw [constraintMatrix_row_13 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 2) (goodTrivector : Vec R 20) 1 = 0
    exact congrFun (goodTriple_contraction 2) 1
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 14 = constraintForcing 14
    rw [constraintMatrix_row_14 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 2) (goodTrivector : Vec R 20) 2 = 0
    exact congrFun (goodTriple_contraction 2) 2
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 15 = constraintForcing 15
    rw [constraintMatrix_row_15 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 2) (goodTrivector : Vec R 20) 3 = 0
    exact congrFun (goodTriple_contraction 2) 3
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 16 = constraintForcing 16
    rw [constraintMatrix_row_16 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 2) (goodTrivector : Vec R 20) 4 = 0
    exact congrFun (goodTriple_contraction 2) 4
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 17 = constraintForcing 17
    rw [constraintMatrix_row_17 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    change contract3 (goodTriple 2) (goodTrivector : Vec R 20) 5 = 0
    exact congrFun (goodTriple_contraction 2) 5
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 18 = constraintForcing 18
    rw [constraintMatrix_row_18 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    rfl
  · change (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).mulVec goodTrivector 19 = constraintForcing 19
    rw [constraintMatrix_row_19 (goodTriple : Fin 3 → Mat R 6) goodTrivector]
    rfl

theorem kernelVector_good :
    kernelVector (goodTriple : Fin 3 → Mat R 6) = (constraintMatrix (goodTriple : Fin 3 → Mat R 6)).det • goodTrivector := by
  rw [kernelVector, ← goodConstraint_goodTrivector, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec]

end Ring

section Field
variable {K : Type*} [Field K] [NeZero (2 : K)]

theorem kernelVector_good_discriminant_ne_zero :
    trivectorDiscriminant (kernelVector (goodTriple : Fin 3 → Mat K 6)) ≠ 0 := by
  rw [kernelVector_good, trivectorDiscriminant_smul, goodTrivector_discriminant]
  have h32 : (-32 : K) ≠ 0 := by
    rw [show (-32 : K) = -(2 : K)^5 by norm_num]
    exact (neg_ne_zero).mpr (pow_ne_zero _ (NeZero.ne _))
  exact mul_ne_zero (pow_ne_zero 4 goodConstraint_det_ne_zero) h32

end Field
end PfaffianDescent
