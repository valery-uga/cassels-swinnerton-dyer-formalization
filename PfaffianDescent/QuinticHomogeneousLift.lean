import PfaffianDescent.QuinticCoordinateReduction

namespace PfaffianDescent
open MvPolynomial
section
variable {K : Type*} [Field K]

/-- A homogeneous vector in the matrix kernel can be corrected by a homogeneous
multiple of the quadratic Pfaffians so that every coordinate is divisible by `x₀`. -/
theorem quintic_homogeneous_boundary_lift (a : Vec K 5) (d : ℕ)
    (v : Fin 5 → MvPolynomial (Fin 4) K) (hd : ∀ i, (v i).IsHomogeneous d)
    (hv : (quinticPolynomialMatrix a).mulVec v = 0) :
    ∃ r : MvPolynomial (Fin 4) K,
      (∀ i, (r * quinticRelations a i).IsHomogeneous d) ∧
      ∀ i, X 0 ∣ v i - r * quinticRelations a i := by
  obtain ⟨s, hs⟩ := quinticPolynomialMatrix_reduced_kernel a v hv
  let r := killVariable 0 s
  have hr (i : Fin 5) : killVariable 0 (v i) = r * quinticBoundaryRelations a i := by
    have h := congrArg (killVariable (K := K) 0) (congrFun hs i)
    simpa only [killVariable_idempotent, Pi.smul_apply, smul_eq_mul, map_mul,
      quinticBoundaryRelations_fixed] using h
  have hprod : (r * quinticBoundaryRelations a 0).IsHomogeneous d := by
    rw [← hr]
    exact killVariable_homogeneous 0 (hd 0)
  refine ⟨r, ?_, ?_⟩
  · by_cases hlt : d < 2
    · have hz : r = 0 := eq_zero_of_mul_homogeneous_lt
        (quinticBoundaryRelations_homogeneous a 0) (quinticBoundaryRelations_zero_ne a) hprod hlt
      intro i
      rw [hz, zero_mul]
      exact (homogeneousSubmodule (Fin 4) K d).zero_mem
    · have he : d - 2 + 2 = d := Nat.sub_add_cancel (Nat.le_of_not_gt hlt)
      have hhom : r.IsHomogeneous (d - 2) := homogeneous_of_mul_right
        (quinticBoundaryRelations_homogeneous a 0) (quinticBoundaryRelations_zero_ne a)
        (he.symm ▸ hprod)
      intro i
      exact he ▸ hhom.mul (quinticRelations_homogeneous a i)
  · intro i
    apply (variable_dvd_iff_reduction_zero 0 _).mpr
    rw [map_sub, map_mul, quinticRelations_reduction, hr]
    change r * quinticBoundaryRelations a i - killVariable 0 (killVariable 0 s) *
      quinticBoundaryRelations a i = 0
    rw [killVariable_idempotent]
    exact sub_self _

end
end PfaffianDescent
