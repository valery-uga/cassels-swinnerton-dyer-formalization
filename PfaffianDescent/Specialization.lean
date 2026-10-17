import PfaffianDescent.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer

namespace PfaffianDescent
open Polynomial

section
variable {R S : Type*} [CommRing R] [CommRing S]

/-- Pfaffians commute with every change of coefficient ring. -/
theorem pf6_map (f : R →+* S) (A : Mat R 6) :
    pf6 (A.map f) = f (pf6 A) := by
  simp only [pf6, Matrix.map_apply, map_add, map_sub, map_mul]

/-- Evaluating a pencil commutes with change of coefficient ring. -/
theorem pencil_map (f : R →+* S) (A : Fin 4 → Mat R 6) (x : Vec R 4) :
    pencil (fun i => (A i).map f) (fun i => f (x i)) = (pencil A x).map f := by
  ext i j
  simp only [pencil, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, map_add, map_mul]

end

section
variable {K : Type*} [Field K]

/-- Divide common powers of the parameter out of a polynomial point on a
homogeneous equation. One coordinate then has nonzero constant coefficient. -/
theorem normalize_polynomial_point {ι : Type*}
    (F : (ι → K[X]) → K[X]) (d : ℕ)
    (hhom : ∀ (c : K[X]) p, F (c • p) = c ^ d * F p)
    (p : ι → K[X]) (hp : p ≠ 0) (hF : F p = 0) :
    ∃ q : ι → K[X], F q = 0 ∧ ∃ i, (q i).coeff 0 ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, p i ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (funext h)
  suffices ∀ n, ∀ p : ι → K[X], p i ≠ 0 → (p i).natDegree = n → F p = 0 →
      ∃ q : ι → K[X], F q = 0 ∧ ∃ j, (q j).coeff 0 ≠ 0 by
    exact this _ p hi rfl hF
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hpi hn hFp
    by_cases hc : ∃ j, (p j).coeff 0 ≠ 0
    · exact ⟨p, hFp, hc⟩
    push Not at hc
    let q : ι → K[X] := fun j => (p j).divX
    have hq : (X : K[X]) • q = p := by
      funext j
      simpa only [Pi.smul_apply, smul_eq_mul, q, hc j, C_0, add_zero] using
        (X_mul_divX_add (p j))
    have hqi : q i ≠ 0 := by
      intro hz
      apply hpi
      have hh := congrFun hq i
      simpa only [Pi.smul_apply, smul_eq_mul, hz, mul_zero] using hh.symm
    have hdegree : (q i).natDegree < n := by
      have hh := congrArg Polynomial.natDegree (congrFun hq i)
      change ((X : K[X]) * q i).natDegree = (p i).natDegree at hh
      rw [mul_comm, natDegree_mul_X hqi, hn] at hh
      omega
    have hFq : F q = 0 := by
      have hh := hhom X q
      rw [hq, hFp] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left (pow_ne_zero d X_ne_zero)
    exact ih _ hdegree q hqi rfl hFq

/-- Specialize a polynomial point of a Pfaffian family at the parameter zero.
No smoothness, flatness, or condition on the special fiber is needed. -/
theorem specialize_polynomial_pfaffian (A : Fin 4 → Mat K[X] 6)
    (h : HasPfaffianPoint A) :
    HasPfaffianPoint (fun i => (A i).map (Polynomial.evalRingHom 0)) := by
  obtain ⟨p, hp, hFp⟩ := h
  obtain ⟨q, hq, i, hi⟩ := normalize_polynomial_point
    (fun x => pf6 (pencil A x)) 3 (pf6_pencil_homogeneous A) p hp hFp
  refine ⟨fun j => (q j).eval 0, ?_, ?_⟩
  · intro hz
    apply hi
    simpa only [coeff_zero_eq_eval_zero, Pi.zero_apply] using congrFun hz i
  · change pf6 (pencil (fun i => (A i).map (Polynomial.evalRingHom 0))
      (fun j => (Polynomial.evalRingHom 0) (q j))) = 0
    rw [pencil_map, pf6_map, hq, map_zero]

/-- Clear a single common denominator in a fraction-field Pfaffian point. -/
theorem clear_pfaffian_denominators {R L : Type*} [CommRing R] [IsDomain R]
    [Field L] [Algebra R L] [IsFractionRing R L]
    (A : Fin 4 → Mat R 6)
    (h : HasPfaffianPoint (fun i => (A i).map (algebraMap R L))) :
    HasPfaffianPoint A := by
  obtain ⟨x, hx, hFx⟩ := h
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) x
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
    rw [map_zero, ← pf6_map, ← pencil_map, hmap, pf6_pencil_homogeneous, hFx, mul_zero]

/-- The complete coordinate specialization step for a rational-function point. -/
theorem specialize_fraction_pfaffian {L : Type*} [Field L]
    [Algebra K[X] L] [IsFractionRing K[X] L]
    (A : Fin 4 → Mat K[X] 6)
    (h : HasPfaffianPoint (fun i => (A i).map (algebraMap K[X] L))) :
    HasPfaffianPoint (fun i => (A i).map (Polynomial.evalRingHom 0)) :=
  specialize_polynomial_pfaffian A (clear_pfaffian_denominators A h)

end
end PfaffianDescent
