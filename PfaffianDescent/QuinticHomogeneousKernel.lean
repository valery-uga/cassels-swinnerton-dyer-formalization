import PfaffianDescent.QuinticHomogeneousLift

namespace PfaffianDescent
open MvPolynomial
section
variable {K : Type*} [Field K]

lemma quinticPolynomialMatrix_quadrics (a : Vec K 5) :
    (quinticPolynomialMatrix a).mulVec (quinticRelations a) = 0 :=
  quinticSyzygyMatrix_quadrics _ _

lemma quintic_kernel_division (a : Vec K 5)
    (v w : Fin 5 → MvPolynomial (Fin 4) K) (r : MvPolynomial (Fin 4) K)
    (hv : (quinticPolynomialMatrix a).mulVec v = 0)
    (hw : ∀ i, v i - r * quinticRelations a i = X 0 * w i) :
    (quinticPolynomialMatrix a).mulVec w = 0 := by
  have he : v - r • quinticRelations a = (X 0 : MvPolynomial (Fin 4) K) • w := by
    funext i
    exact hw i
  have hh := congrArg (quinticPolynomialMatrix a).mulVec he
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hv,
    quinticPolynomialMatrix_quadrics, smul_zero, sub_zero] at hh
  funext i
  exact (mul_eq_zero.mp (congrFun hh.symm i)).resolve_left (MvPolynomial.X_ne_zero 0)

/-- Every homogeneous polynomial vector in the quintic matrix kernel is a
multiple of its quadratic Pfaffian vector. -/
theorem quintic_homogeneous_kernel (a : Vec K 5) (d : ℕ)
    (v : Fin 5 → MvPolynomial (Fin 4) K) (hd : ∀ i, (v i).IsHomogeneous d)
    (hv : (quinticPolynomialMatrix a).mulVec v = 0) :
    ∃ r : MvPolynomial (Fin 4) K, v = r • quinticRelations a := by
  classical
  induction d generalizing v with
  | zero =>
    obtain ⟨r, hr, hdiv⟩ := quintic_homogeneous_boundary_lift a 0 v hd hv
    choose w hw using hdiv
    have hz (i : Fin 5) : w i = 0 := by
      have hh : (w i * X 0).IsHomogeneous 0 := by
        rw [mul_comm, ← hw]
        exact (hd i).sub (hr i)
      exact eq_zero_of_mul_homogeneous_lt (isHomogeneous_X K (0 : Fin 4))
        (MvPolynomial.X_ne_zero 0) hh (by decide)
    refine ⟨r, ?_⟩
    funext i
    have hi := hw i
    rw [hz, mul_zero] at hi
    exact sub_eq_zero.mp hi
  | succ d ih =>
    obtain ⟨r, hr, hdiv⟩ := quintic_homogeneous_boundary_lift a (d + 1) v hd hv
    choose w hw using hdiv
    have hwd (i : Fin 5) : (w i).IsHomogeneous d := by
      apply homogeneous_of_mul_right (isHomogeneous_X K (0 : Fin 4)) (MvPolynomial.X_ne_zero 0)
      rw [mul_comm, ← hw]
      exact (hd i).sub (hr i)
    obtain ⟨s, hs⟩ := ih w hwd (quintic_kernel_division a v w r hv hw)
    refine ⟨r + X 0 * s, ?_⟩
    funext i
    have hi := hw i
    rw [hs] at hi
    change v i - r * quinticRelations a i = X 0 * (s * quinticRelations a i) at hi
    change v i = (r + X 0 * s) * quinticRelations a i
    linear_combination hi

end
end PfaffianDescent
