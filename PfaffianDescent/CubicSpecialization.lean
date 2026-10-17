import PfaffianDescent.PolynomialNormalization
import PfaffianDescent.CubicLinear

namespace PfaffianDescent
open Polynomial

section
variable {K : Type*} [Field K] {n : ℕ}

/-- A polynomial family of cubic forms specializes any projective polynomial point. -/
theorem specialize_polynomial_cubic_at (c : Cubic K[X] n) (t : K)
    (p : Vec K[X] n) (hp : p ≠ 0) (hF : c.eval p = 0) :
    ∃ x : Vec K n, x ≠ 0 ∧ (c.map (evalRingHom t)).eval x = 0 := by
  obtain ⟨q, hq, i, hi⟩ := normalize_polynomial_relation t (fun p => c.eval p = 0)
    (fun q h => by
      rw [Cubic.eval_smul] at h
      exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 (X_sub_C_ne_zero t))) p hp hF
  refine ⟨fun j => (q j).eval t, ?_, ?_⟩
  · intro hz
    exact hi (congrFun hz i)
  · change (c.map (evalRingHom t)).eval (fun j => (evalRingHom t) (q j)) = 0
    rw [Cubic.eval_map, hq, map_zero]

end

section
variable {R L : Type*} [CommRing R] [IsDomain R] [Field L] [Algebra R L] [IsFractionRing R L]
    {n : ℕ}

/-- Clear denominators in a homogeneous cubic equation without losing the nonzero point. -/
theorem clear_cubic_denominators (c : Cubic R n) (x : Vec L n) (hx : x ≠ 0)
    (hF : (c.map (algebraMap R L)).eval x = 0) :
    ∃ p : Vec R n, p ≠ 0 ∧ c.eval p = 0 := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) x
  choose p hp using hb
  have hmap : (fun i => algebraMap R L (p i)) = algebraMap R L b • x := by
    funext i
    change algebraMap R L (p i) = algebraMap R L b * x i
    simpa only [Algebra.smul_def] using hp i
  have hbR : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.property
  have hbL : algebraMap R L b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R L)).mpr hbR
  refine ⟨p, ?_, ?_⟩
  · intro hz
    have hh : algebraMap R L b • x = 0 := by
      rw [← hmap, hz]
      funext i
      exact map_zero _
    exact hx ((smul_eq_zero.mp hh).resolve_left hbL)
  · apply IsFractionRing.injective R L
    rw [map_zero, ← Cubic.eval_map, hmap, Cubic.eval_smul, hF, mul_zero]

end

section
variable {K L : Type*} [Field K] [Field L] [Algebra K[X] L] [IsFractionRing K[X] L] {n : ℕ}

/-- Rational-function points of cubic families specialize at any ground-field parameter. -/
theorem specialize_fraction_cubic_at (c : Cubic K[X] n) (t : K)
    (x : Vec L n) (hx : x ≠ 0) (hF : (c.map (algebraMap K[X] L)).eval x = 0) :
    ∃ p : Vec K n, p ≠ 0 ∧ (c.map (evalRingHom t)).eval p = 0 := by
  obtain ⟨q, hq, he⟩ := clear_cubic_denominators c x hx hF
  exact specialize_polynomial_cubic_at c t q hq he

end
end PfaffianDescent
