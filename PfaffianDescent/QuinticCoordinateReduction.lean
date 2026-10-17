import PfaffianDescent.QuinticPolynomialRelations
import PfaffianDescent.QuinticBoundaryKernel
import PfaffianDescent.PolynomialCoordinateReduction

namespace PfaffianDescent
open MvPolynomial
section
variable {K : Type*} [Field K]

noncomputable def quinticPolynomialMatrix (a : Vec K 5) : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 4) K) :=
  quinticSyzygyMatrix (fun i => C (a i)) X

noncomputable def quinticBoundaryRelations (a : Vec K 5) : Fin 5 → MvPolynomial (Fin 4) K :=
  quinticQuadrics (fun i => C (a i)) ![0, X 1, X 2, X 3]

lemma killVariable_zero_coordinates :
    (fun i : Fin 4 => killVariable (K := K) 0 (X i)) = ![0, X 1, X 2, X 3] := by
  funext i
  fin_cases i <;> simp

lemma quinticRelations_reduction (a : Vec K 5) (i : Fin 5) :
    killVariable 0 (quinticRelations a i) = quinticBoundaryRelations a i := by
  change (killVariable 0).toRingHom (quinticQuadrics (fun j => C (a j)) X i) = _
  rw [quinticQuadrics_map]
  simp only [Function.comp_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, killVariable_C,
    killVariable_zero_coordinates]
  rfl

lemma quinticBoundaryRelations_homogeneous (a : Vec K 5) (i : Fin 5) :
    (quinticBoundaryRelations a i).IsHomogeneous 2 := by
  rw [← quinticRelations_reduction]
  exact killVariable_homogeneous 0 (quinticRelations_homogeneous a i)

lemma quinticBoundaryRelations_fixed (a : Vec K 5) (i : Fin 5) :
    killVariable 0 (quinticBoundaryRelations a i) = quinticBoundaryRelations a i := by
  rw [← quinticRelations_reduction, killVariable_idempotent]

lemma quinticBoundaryRelations_zero_ne (a : Vec K 5) :
    quinticBoundaryRelations a 0 ≠ 0 := by
  change 0 * X 2 - X 1 ^ 2 ≠ (0 : MvPolynomial (Fin 4) K)
  simp only [zero_mul, zero_sub, neg_ne_zero]
  exact pow_ne_zero _ (MvPolynomial.X_ne_zero (1 : Fin 4))

lemma quinticPolynomialMatrix_reduction (a : Vec K 5) :
    (quinticPolynomialMatrix a).map (killVariable (K := K) 0) =
      quinticSyzygyMatrix (fun i => C (a i)) ![0, X 1, X 2, X 3] := by
  change (quinticSyzygyMatrix (fun i => C (a i)) X).map (killVariable 0).toRingHom = _
  rw [quinticSyzygyMatrix_map]
  simp only [Function.comp_def, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, killVariable_C,
    killVariable_zero_coordinates]

lemma quinticPolynomialMatrix_reduced_kernel (a : Vec K 5)
    (v : Fin 5 → MvPolynomial (Fin 4) K) (hv : (quinticPolynomialMatrix a).mulVec v = 0) :
    ∃ r : MvPolynomial (Fin 4) K,
      (fun i => killVariable 0 (v i)) = r • quinticBoundaryRelations a := by
  have he : (quinticSyzygyMatrix (fun i => C (a i)) ![0, X 1, X 2, X 3]).mulVec
      (fun i => killVariable 0 (v i)) = 0 := by
    rw [← quinticPolynomialMatrix_reduction]
    funext i
    have h := RingHom.map_mulVec (killVariable (K := K) 0).toRingHom (quinticPolynomialMatrix a) v i
    rw [hv] at h
    exact h.symm.trans (map_zero _)
  exact quintic_boundary_kernel (fun i => C (a i)) ![X 1, X 2, X 3]
    (show Prime (X 1 : MvPolynomial (Fin 4) K) from MvPolynomial.X_prime) (by simp) _ he

end
end PfaffianDescent
