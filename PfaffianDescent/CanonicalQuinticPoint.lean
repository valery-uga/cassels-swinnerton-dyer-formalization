import PfaffianDescent.CubicRemainder
import PfaffianDescent.QuinticPowerBasis
import PfaffianDescent.Deformation

namespace PfaffianDescent
open Module

section Ring
variable {R S : Type*} [CommRing R] [CommRing S]

theorem reductionRemainder_map (f : R →+* S) (u : Vec R 25) :
    reductionRemainder (fun j => f (u j)) = fun j => f (reductionRemainder u j) := by
  funext i
  fin_cases i <;> rfl

theorem remainderCubic_at_rational (r : Vec R 5) (z : R) :
    remainderCubic r (rationalCubicCoordinates z) = ∑ i : Fin 5, r i * z^(i : ℕ) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change r 0 * 1^3 + r 1 * 1^2 * z + r 2 * 1^2 * z^2 +
    r 3 * 1^2 * z^3 + r 4 * 1 * z * z^3 =
      r 0 * z^0 + (r 1 * z^1 + (r 2 * z^2 + (r 3 * z^3 + r 4 * z^4)))
  ring

end Ring

section Field
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L]

theorem quintic_root_of_power_basis (α : L) (b : Basis (Fin 5) K L)
    (hb : ∀ i, b i = α^(i : ℕ)) :
    ∃ a : Vec K 5, quinticRelation (fun i => algebraMap K L (a i)) α := by
  obtain ⟨a, ha⟩ := quintic_relation_of_power_basis α b hb
  refine ⟨a, ?_⟩
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at ha
  change α^5 + (algebraMap K L (a 0) * α^0 + (algebraMap K L (a 1) * α^1 +
    (algebraMap K L (a 2) * α^2 + (algebraMap K L (a 3) * α^3 + algebraMap K L (a 4) * α^4)))) = 0 at ha
  unfold quinticRelation
  linear_combination ha

theorem remainder_zero_of_power_basis (α : L) (b : Basis (Fin 5) K L)
    (hb : ∀ i, b i = α^(i : ℕ)) (r : Vec K 5)
    (hr : remainderCubic (fun i => algebraMap K L (r i)) (rationalCubicCoordinates α) = 0) : r = 0 := by
  have hs : ∑ i : Fin 5, r i • b i = 0 := by
    simp only [hb, Algebra.smul_def]
    rw [← remainderCubic_at_rational]
    exact hr
  exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent r hs)

/-- A cubic containing a degree-five point in rational-normal-cubic coordinates
has a ground-field rational point, with the Pfaffian presentation constructed inside the proof. -/
theorem canonical_quintic_point_descent (α : L) (b : Basis (Fin 5) K L)
    (hb : ∀ i, b i = α^(i : ℕ)) (c : Vec K 20)
    (hF : coordinateCubic (fun i => algebraMap K L (c i)) (rationalCubicCoordinates α) = 0) :
    ∃ x : Vec K 4, x ≠ 0 ∧ coordinateCubic c x = 0 := by
  obtain ⟨a, ha⟩ := quintic_root_of_power_basis α b hb
  let u := cubicReduction a c
  have hformula := cubic_reduction_formula_map (algebraMap K L) a c (rationalCubicCoordinates α)
  rw [hF, quinticQuadrics_at_root _ _ ha] at hformula
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at hformula
  have hr : reductionRemainder u = 0 := by
    apply remainder_zero_of_power_basis α b hb
    rw [← reductionRemainder_map]
    exact hformula.symm
  let ell := reductionLinearForms u
  obtain ⟨x, hx, hpx⟩ := pfaffian_to_point (quinticPencil a ell) (quinticPencil_alternating a ell)
  refine ⟨x, hx, ?_⟩
  have heq := cubic_reduction_formula a c x
  change coordinateCubic c x =
    (∑ i, linearValue (ell i) x * quinticQuadrics a x i) + remainderCubic (reductionRemainder u) x at heq
  rw [hr, remainderCubic_zero, add_zero, ← quinticMatrix_pfaffian, ← quinticPencil_eval] at heq
  exact heq.trans hpx

end Field
end PfaffianDescent
