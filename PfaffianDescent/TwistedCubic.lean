import PfaffianDescent.QuinticDescent
import Mathlib.RingTheory.Polynomial.UniqueFactorization

namespace PfaffianDescent
open Polynomial Module
open scoped BigOperators

namespace Cubic
section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Restriction to the affine chart `(1,t,t²,t³)` of the split twisted cubic. -/
noncomputable def twistedPolynomial (c : Cubic R 4) : R[X] :=
  ∑ i, monomial (i.1.val + i.2.1.val + i.2.2.val) (c i)

theorem twistedPolynomial_eval₂ (f : R →+* S) (c : Cubic R 4) (a : S) :
    eval₂ f a c.twistedPolynomial = (c.map f).eval (fun i => a^(i : ℕ)) := by
  simp only [twistedPolynomial, eval₂_finsetSum, eval₂_monomial, Cubic.eval, Cubic.map]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pow_add, mul_assoc]

theorem twistedPolynomial_degree_le (c : Cubic R 4) : c.twistedPolynomial.natDegree ≤ 9 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply (natDegree_monomial_le _).trans
  have h₁ := i.1.isLt
  have h₂ := i.2.1.isLt
  have h₃ := i.2.2.isLt
  omega

theorem twistedPolynomial_coeff_nine (c : Cubic R 4) :
    c.twistedPolynomial.coeff 9 = c (3, 3, 3) := by
  simp [twistedPolynomial, Fintype.sum_prod_type, Fin.sum_univ_four,
    coeff_monomial]

theorem eval_last_coordinate (c : Cubic R 4) :
    c.eval (Pi.single 3 1) = c (3, 3, 3) := by
  simp [Cubic.eval, Fintype.sum_prod_type, Pi.single_apply]

end
end Cubic

section
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- A quintic polynomial has an irreducible factor of degree at most two or five. -/
theorem quintic_polynomial_small_factor (q : K[X]) (hq : q.natDegree = 5) :
    ∃ r : K[X], Irreducible r ∧ r ∣ q ∧ (r.natDegree ≤ 2 ∨ r.natDegree = 5) := by
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  by_cases hirr : Irreducible q
  · exact ⟨q, hirr, dvd_refl q, Or.inr hq⟩
  have hqu : ¬ IsUnit q := not_isUnit_of_natDegree_pos q (by omega)
  rw [irreducible_iff_lt_natDegree_lt hq0 hqu] at hirr
  push Not at hirr
  obtain ⟨p, hp, hd, hdvd⟩ := hirr
  have hdp : 0 < p.natDegree ∧ p.natDegree ≤ 2 := by
    simpa only [hq, Nat.reduceDiv, Finset.mem_Ioc] using hd
  obtain ⟨r, hr, hrdvd⟩ := exists_irreducible_of_natDegree_pos hdp.1
  exact ⟨r, hr, hrdvd.trans hdvd, Or.inl ((natDegree_le_of_dvd hrdvd hp.ne_zero).trans hdp.2)⟩

/-- A quintic factor in the intersection with a split twisted cubic produces a rational point. -/
theorem cubic_descent_of_twisted_quintic_factor (c : Cubic K 4) (q : K[X])
    (hq : q.natDegree = 5) (hqdvd : q ∣ c.twistedPolynomial) :
    ∃ x : Vec K 4, x ≠ 0 ∧ c.eval x = 0 := by
  obtain ⟨r, hr, hrq, hd⟩ := quintic_polynomial_small_factor q hq
  let : Fact (Irreducible r) := ⟨hr⟩
  let L := AdjoinRoot r
  let : FiniteDimensional K L := Module.Finite.of_basis (AdjoinRoot.powerBasis hr.ne_zero).basis
  have hdim : finrank K L = r.natDegree := by
    rw [(AdjoinRoot.powerBasis hr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  let a : L := AdjoinRoot.root r
  let p : Vec L 4 := fun i => a^(i : ℕ)
  have hp : p ≠ 0 := by
    intro h
    have hh := congrFun h 0
    exact one_ne_zero (by simpa only [p, Fin.val_zero, pow_zero, Pi.zero_apply] using hh)
  have he : eval₂ (algebraMap K L) a c.twistedPolynomial = 0 := by
    obtain ⟨s, hs⟩ := hrq.trans hqdvd
    rw [hs, eval₂_mul]
    have hroot : eval₂ (algebraMap K L) a r = 0 := by
      change eval₂ (algebraMap K (AdjoinRoot r)) (AdjoinRoot.root r) r = 0
      rw [AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.eval₂_root r
    rw [hroot, zero_mul]
  rw [Cubic.twistedPolynomial_eval₂] at he
  rcases hd with hd | hd
  · exact cubic_degree_le_two_secant (hdim.trans_le hd) c p hp he
  · exact cubic_degree_five_descent (hdim.trans hd) c p hp he

end

section
variable {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]

/-- The residual intersection `9 = 4 + 5` on a split twisted cubic. -/
theorem canonical_quartic_point_descent (c : Cubic K 4) (a : L)
    (ha : (minpoly K a).natDegree = 4)
    (hF : (c.map (algebraMap K L)).eval (fun i => a^(i : ℕ)) = 0) :
    ∃ x : Vec K 4, x ≠ 0 ∧ c.eval x = 0 := by
  by_cases hc : c (3, 3, 3) = 0
  · refine ⟨Pi.single 3 1, ?_, ?_⟩
    · intro h
      have hh := congrFun h 3
      exact one_ne_zero (by simpa only [Pi.single_eq_same, Pi.zero_apply] using hh)
    · rw [Cubic.eval_last_coordinate, hc]
  have hdeg : c.twistedPolynomial.natDegree = 9 := by
    apply Nat.le_antisymm (Cubic.twistedPolynomial_degree_le c)
    apply le_natDegree_of_ne_zero
    rwa [Cubic.twistedPolynomial_coeff_nine]
  have he : aeval a c.twistedPolynomial = 0 := by
    change eval₂ (algebraMap K L) a c.twistedPolynomial = 0
    rw [Cubic.twistedPolynomial_eval₂]
    exact hF
  obtain ⟨q, hq⟩ := minpoly.dvd K a he
  have hpoly0 : c.twistedPolynomial ≠ 0 := by intro h; simp [h] at hdeg
  have hg0 : minpoly K a ≠ 0 := by intro h; simp [h] at ha
  have hq0 : q ≠ 0 := by intro h; rw [h, mul_zero] at hq; exact hpoly0 hq
  have hdq : q.natDegree = 5 := by
    have hmul := natDegree_mul hg0 hq0
    rw [← hq, hdeg, ha] at hmul
    omega
  exact cubic_descent_of_twisted_quintic_factor c q hdq ⟨minpoly K a, by rw [mul_comm]; exact hq⟩

end
end PfaffianDescent
