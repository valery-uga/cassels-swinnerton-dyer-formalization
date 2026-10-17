import PfaffianDescent.MultivariateCubic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Funext

namespace PfaffianDescent
open Module
open scoped BigOperators

section
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The monic quintic relation for a power basis of a finite algebra, which
may be a product of fields rather than a field. -/
theorem quintic_root_of_algebra_power_basis (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) :
    ∃ r : Vec K 5, quinticRelation (fun i => algebraMap K A (r i)) a := by
  let r : Vec K 5 := fun i => -b.repr (a^5) i
  have h : a^5 + ∑ i : Fin 5, algebraMap K A (r i) * a^(i : ℕ) = 0 := by
    have he := b.sum_repr (a^5)
    simp only [hb, Algebra.smul_def] at he
    simp only [r, map_neg, neg_mul, Finset.sum_neg_distrib, he, add_neg_cancel]
  refine ⟨r, ?_⟩
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at h
  change a^5 + (algebraMap K A (r 0) * a^0 + (algebraMap K A (r 1) * a^1 +
    (algebraMap K A (r 2) * a^2 + (algebraMap K A (r 3) * a^3 + algebraMap K A (r 4) * a^4)))) = 0 at h
  unfold quinticRelation
  linear_combination h

theorem remainder_zero_of_algebra_power_basis (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) (r : Vec K 5)
    (hr : remainderCubic (fun i => algebraMap K A (r i)) (rationalCubicCoordinates a) = 0) : r = 0 := by
  have hs : ∑ i : Fin 5, r i • b i = 0 := by
    simp only [hb, Algebra.smul_def]
    rw [← remainderCubic_at_rational]
    exact hr
  exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent r hs)

/-- An explicit Pfaffian presentation over the ground field for every cubic
vanishing at a quintic-algebra point in rational-normal-cubic coordinates.
The algebra need not be a field or reduced. -/
theorem canonical_algebra_quintic_presentation (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) (c : Vec K 20)
    (hF : coordinateCubic (fun i => algebraMap K A (c i)) (rationalCubicCoordinates a) = 0) :
    ∃ P : Fin 4 → Mat K 6, (∀ i, IsAlternating (P i)) ∧
      ∀ x : Vec K 4, coordinateCubic c x = pf6 (pencil P x) := by
  obtain ⟨r, hr⟩ := quintic_root_of_algebra_power_basis a b hb
  let u := cubicReduction r c
  have hformula := cubic_reduction_formula_map (algebraMap K A) r c (rationalCubicCoordinates a)
  rw [hF, quinticQuadrics_at_root _ _ hr] at hformula
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at hformula
  have hu : reductionRemainder u = 0 := by
    apply remainder_zero_of_algebra_power_basis a b hb
    rw [← reductionRemainder_map]
    exact hformula.symm
  let ell := reductionLinearForms u
  refine ⟨quinticPencil r ell, quinticPencil_alternating r ell, ?_⟩
  intro x
  have he := cubic_reduction_formula r c x
  change coordinateCubic c x =
    (∑ i, linearValue (ell i) x * quinticQuadrics r x i) + remainderCubic (reductionRemainder u) x at he
  rw [hu, remainderCubic_zero, add_zero, ← quinticMatrix_pfaffian, ← quinticPencil_eval] at he
  exact he

/-- The same presentation for the tensor representation of a cubic. -/
theorem canonical_algebra_quintic_tensor_presentation (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) (c : Cubic K 4)
    (hF : (c.map (algebraMap K A)).eval (rationalCubicCoordinates a) = 0) :
    ∃ P : Fin 4 → Mat K 6, (∀ i, IsAlternating (P i)) ∧
      ∀ x : Vec K 4, c.eval x = pf6 (pencil P x) := by
  have he : coordinateCubic (fun i => algebraMap K A (c.coordinates i)) (rationalCubicCoordinates a) = 0 := by
    rw [← Cubic.coordinates_map, Cubic.eval_coordinates]
    exact hF
  obtain ⟨P, hP, hPx⟩ := canonical_algebra_quintic_presentation a b hb c.coordinates he
  refine ⟨P, hP, ?_⟩
  intro x
  rw [← Cubic.eval_coordinates c x]
  exact hPx x

end

section
variable {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]

/-- The presentation is an equality of actual multivariate polynomials. -/
theorem canonical_algebra_quintic_polynomial_presentation (a : A) (b : Basis (Fin 5) K A)
    (hb : ∀ i, b i = a^(i : ℕ)) (f : MvPolynomial (Fin 4) K) (hf : f.IsHomogeneous 3)
    (hF : MvPolynomial.eval₂ (algebraMap K A) (rationalCubicCoordinates a) f = 0) :
    ∃ P : Fin 4 → Mat K 6, (∀ i, IsAlternating (P i)) ∧ (pfaffianCubic P).toMvPolynomial = f := by
  obtain ⟨c, rfl⟩ := homogeneous_cubic_has_tensor f hf
  rw [Cubic.eval_toMvPolynomial] at hF
  obtain ⟨P, hP, he⟩ := canonical_algebra_quintic_tensor_presentation a b hb c hF
  refine ⟨P, hP, ?_⟩
  apply MvPolynomial.funext
  intro x
  change MvPolynomial.eval₂ (RingHom.id K) x (pfaffianCubic P).toMvPolynomial =
    MvPolynomial.eval₂ (RingHom.id K) x c.toMvPolynomial
  rw [Cubic.eval_toMvPolynomial, Cubic.eval_toMvPolynomial]
  change (pfaffianCubic P).eval x = c.eval x
  rw [eval_pfaffianCubic]
  exact (he x).symm

end
end PfaffianDescent
