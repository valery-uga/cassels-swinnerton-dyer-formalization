import PfaffianDescent.Cubic
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Residual quadratics on lines through cubic points

If a line through a point of a cubic is written as `p + t d`, its cubic
equation has the known factor `t`.  This file records the remaining quadratic
polynomial, its behaviour under base change, and the fact that any of its
roots gives another point on the cubic.  These are the algebraic first steps
in the quadratic-pair construction used in the Segre--Manin--Kollár
unirationality argument.
-/

namespace PfaffianDescent
namespace Cubic

open Polynomial Module

universe u

section

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ}

/-- After removing the known root `t = 0`, the cubic restricted to the line
through `p` in direction `d`. -/
noncomputable def lineResidualPolynomial (c : Cubic R n) (p d : Vec R n) : R[X] :=
  C (c.mixed p d) + C (c.mixed d p) * X + C (c.eval d) * X ^ 2

/-- Evaluation of the residual line polynomial. -/
theorem eval₂_lineResidualPolynomial (f : R →+* S) (c : Cubic R n)
    (p d : Vec R n) (a : S) :
    Polynomial.eval₂ f a (lineResidualPolynomial c p d) =
      f (c.mixed p d) + a * f (c.mixed d p) + a ^ 2 * f (c.eval d) := by
  simp only [lineResidualPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_C,
    Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_pow]
  ring

/-- The restriction of a cubic to a line through a cubic point factors by the
line parameter, with quotient `lineResidualPolynomial`. -/
theorem eval_line_eq_mul_lineResidualPolynomial
    (f : R →+* S) (c : Cubic R n) (p d : Vec R n)
    (hp : c.eval p = 0) (a : S) :
    (c.map f).eval ((fun i => f (p i)) + a • (fun i => f (d i))) =
      a * Polynomial.eval₂ f a (lineResidualPolynomial c p d) := by
  rw [show (fun i => f (p i)) + a • (fun i => f (d i)) =
    (1 : S) • (fun i => f (p i)) + a • (fun i => f (d i)) by simp,
    Cubic.eval_line, eval₂_lineResidualPolynomial]
  simp only [Cubic.eval_map, Cubic.mixed_map, map_zero, hp, one_pow, one_mul]
  ring

/-- Residual line polynomials commute with arbitrary coefficient extension. -/
theorem map_lineResidualPolynomial (f : R →+* S) (c : Cubic R n) (p d : Vec R n) :
    Polynomial.map f (lineResidualPolynomial c p d) =
      lineResidualPolynomial (c.map f) (fun i => f (p i)) (fun i => f (d i)) := by
  simp [lineResidualPolynomial, Cubic.mixed_map, Cubic.eval_map]

/-- A root of the residual line polynomial yields a point on the cubic. -/
theorem eval_linePoint_of_lineResidual_root
    (f : R →+* S) (c : Cubic R n) (p d : Vec R n)
    (hp : c.eval p = 0) (a : S)
    (hroot : Polynomial.eval₂ f a (lineResidualPolynomial c p d) = 0) :
    (c.map f).eval ((fun i => f (p i)) + a • (fun i => f (d i))) = 0 := by
  rw [eval_line_eq_mul_lineResidualPolynomial f c p d hp a, hroot, mul_zero]

end

section

variable {K : Type u} [Field K] {n : ℕ}

/-- If the secant coefficient at the original point is nonzero, a residual
root cannot be the original line parameter `0`. -/
theorem lineResidual_root_ne_zero_of_mixed_ne_zero
    {L : Type u} [Field L] (f : K →+* L) (c : Cubic K n) (p d : Vec K n)
    (hsec : c.mixed p d ≠ 0) (a : L)
    (hroot : Polynomial.eval₂ f a (lineResidualPolynomial c p d) = 0) :
    a ≠ 0 := by
  intro ha
  rw [ha, eval₂_lineResidualPolynomial] at hroot
  have hmap : f (c.mixed p d) = 0 := by
    simpa using hroot
  exact hsec (f.injective (by simpa using hmap))

/-- A line point obtained from a non-cubic direction through a nonzero cubic
point has nonzero homogeneous coordinates after every field extension. -/
theorem linePoint_ne_zero_of_eval_zero_eval_ne_zero
    {L : Type*} [Field L] (f : K →+* L) (c : Cubic K n) (p d : Vec K n)
    (hp0 : p ≠ 0) (hp : c.eval p = 0) (hdir : c.eval d ≠ 0) (a : L) :
    (fun i => f (p i)) + a • (fun i => f (d i)) ≠ 0 := by
  intro hzero
  by_cases ha : a = 0
  · apply hp0
    funext i
    apply f.injective
    have hi := congrFun hzero i
    simpa [ha] using hi
  · have hline : (fun i => f (p i)) = (-a) • (fun i => f (d i)) := by
      simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hzero
    have heval := congrArg (fun x => (c.map f).eval x) hline
    rw [Cubic.eval_map, Cubic.eval_smul, Cubic.eval_map, hp, map_zero] at heval
    exact (mul_ne_zero (pow_ne_zero 3 (neg_ne_zero.mpr ha))
      ((map_ne_zero f).mpr hdir)) heval.symm

/-- A residual root with nonzero parameter gives a projective point different
from the original point: its coordinates are not a scalar multiple of the
original coordinates. -/
theorem linePoint_not_smul_basePoint_of_eval_zero_eval_ne_zero
    {L : Type u} [Field L] (f : K →+* L) (c : Cubic K n) (p d : Vec K n)
    (hp : c.eval p = 0) (hdir : c.eval d ≠ 0)
    {a : L} (ha : a ≠ 0) (b : L) :
    (fun i => f (p i)) + a • (fun i => f (d i)) ≠ b • (fun i => f (p i)) := by
  intro hzero
  have hav : a • (fun i => f (d i)) = b • (fun i => f (p i)) - (fun i => f (p i)) := by
    rw [eq_sub_iff_add_eq]
    simpa only [add_comm] using hzero
  have hline : (fun i => f (d i)) = (a⁻¹ * (b - 1)) • (fun i => f (p i)) := by
    calc
      (fun i => f (d i)) = (a⁻¹ * a) • (fun i => f (d i)) := by
        rw [inv_mul_cancel₀ ha, one_smul]
      _ = a⁻¹ • (a • (fun i => f (d i))) := by
        rw [smul_smul]
      _ = a⁻¹ • (b • (fun i => f (p i)) - (fun i => f (p i))) := by rw [hav]
      _ = (a⁻¹ * (b - 1)) • (fun i => f (p i)) := by
        funext i
        change a⁻¹ * (b * f (p i) - f (p i)) = (a⁻¹ * (b - 1)) * f (p i)
        ring
  have heval := congrArg (fun x => (c.map f).eval x) hline
  rw [Cubic.eval_map, Cubic.eval_smul, Cubic.eval_map, hp, map_zero] at heval
  have hmap : f (c.eval d) = 0 := by simpa using heval
  exact hdir (f.injective (by simpa using hmap))

/-- The quadratic coefficient of the residual line polynomial is the cubic
value of the line direction. -/
theorem lineResidualPolynomial_coeff_two (c : Cubic K n) (p d : Vec K n) :
    (lineResidualPolynomial c p d).coeff 2 = c.eval d := by
  simp [lineResidualPolynomial]

/-- A direction outside the cubic gives a genuine quadratic residual
polynomial. -/
theorem lineResidualPolynomial_natDegree_eq_two (c : Cubic K n) (p d : Vec K n)
    (hdir : c.eval d ≠ 0) :
    (lineResidualPolynomial c p d).natDegree = 2 := by
  apply Nat.le_antisymm
  · rw [lineResidualPolynomial]
    calc
      (C (c.mixed p d) + C (c.mixed d p) * X + C (c.eval d) * X ^ 2).natDegree ≤
          max (C (c.mixed p d) + C (c.mixed d p) * X).natDegree
            (C (c.eval d) * X ^ 2).natDegree := natDegree_add_le _ _
      _ ≤ max (max (C (c.mixed p d)).natDegree
            (C (c.mixed d p) * X).natDegree)
            (C (c.eval d) * X ^ 2).natDegree :=
        max_le_max_right _ (natDegree_add_le _ _)
      _ ≤ max (max 0 (0 + 1)) (0 + 2) := by
        apply max_le
        · apply max_le
          · calc
              (C (c.mixed p d)).natDegree = 0 := natDegree_C _
              _ ≤ max (max 0 (0 + 1)) (0 + 2) := by norm_num
          · calc
              (C (c.mixed d p) * X).natDegree ≤
                (C (c.mixed d p)).natDegree + X.natDegree := natDegree_mul_le
              _ = 0 + 1 := by simp
              _ ≤ max (max 0 (0 + 1)) (0 + 2) := by norm_num
        · calc
            (C (c.eval d) * X ^ 2).natDegree ≤
              (C (c.eval d)).natDegree + (X ^ 2).natDegree := natDegree_mul_le
            _ = 0 + 2 := by simp
            _ ≤ max (max 0 (0 + 1)) (0 + 2) := by norm_num
      _ = 2 := by norm_num
  · apply le_natDegree_of_ne_zero
    rw [lineResidualPolynomial_coeff_two]
    exact hdir

/-- If the residual quadratic on a line is irreducible, its root produces a
nonzero cubic point over a quadratic field extension. -/
theorem exists_quadratic_lineResidual_point
    (c : Cubic K n) (p d : Vec K n)
    (hp0 : p ≠ 0) (hp : c.eval p = 0) (hdir : c.eval d ≠ 0)
    (hirr : Irreducible (lineResidualPolynomial c p d)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (x : Vec L n), finrank K L = 2 ∧ x ≠ 0 ∧
        (c.map (algebraMap K L)).eval x = 0 := by
  let q := lineResidualPolynomial c p d
  let _ : Fact (Irreducible q) := ⟨hirr⟩
  let L := AdjoinRoot q
  let _ : FiniteDimensional K L :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hirr.ne_zero).basis
  let a : L := AdjoinRoot.root q
  let x : Vec L n := (fun i => algebraMap K L (p i)) +
    a • (fun i => algebraMap K L (d i))
  have hroot : Polynomial.eval₂ (algebraMap K L) a q = 0 := by
    change Polynomial.eval₂ (algebraMap K (AdjoinRoot q)) (AdjoinRoot.root q) q = 0
    rw [AdjoinRoot.algebraMap_eq]
    exact AdjoinRoot.eval₂_root q
  have hdegree : q.natDegree = 2 :=
    lineResidualPolynomial_natDegree_eq_two c p d hdir
  have hdim : finrank K L = q.natDegree := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  refine ⟨L, inferInstance, inferInstance, inferInstance, x, hdim.trans hdegree, ?_, ?_⟩
  · exact linePoint_ne_zero_of_eval_zero_eval_ne_zero (algebraMap K L)
      c p d hp0 hp hdir a
  · exact eval_linePoint_of_lineResidual_root (algebraMap K L) c p d hp a hroot

/-- A quadratic polynomial over a field that is not irreducible has a
ground-field root. -/
theorem exists_root_of_natDegree_two_of_not_irreducible
    (q : K[X]) (hq : q.natDegree = 2) (hirr : ¬ Irreducible q) :
    ∃ a : K, q.eval a = 0 := by
  have hq0 : q ≠ 0 := by
    intro h
    simp [h] at hq
  have hqu : ¬ IsUnit q := not_isUnit_of_natDegree_pos q (by omega)
  rw [irreducible_iff_lt_natDegree_lt hq0 hqu] at hirr
  push Not at hirr
  obtain ⟨r, hrmonic, hrdeg, hrdvd⟩ := hirr
  have hrbounds : 0 < r.natDegree ∧ r.natDegree ≤ 1 := by
    simpa only [hq, Nat.reduceDiv, Finset.mem_Ioc] using hrdeg
  have hrpos : 0 < r.natDegree := hrbounds.1
  have hrle : r.natDegree ≤ 1 := hrbounds.2
  have hrnat : r.natDegree = 1 := by omega
  have hr0 : r ≠ 0 := by
    intro h
    simp [h] at hrpos
  have hrdegree : r.degree = 1 := by
    rw [degree_eq_natDegree hr0, hrnat]
    norm_num
  obtain ⟨a, ha⟩ := exists_root_of_degree_eq_one hrdegree
  refine ⟨a, ?_⟩
  obtain ⟨s, hs⟩ := hrdvd
  rw [hs, eval_mul, ha]
  exact zero_mul _

/-- In the reducible case, a residual quadratic supplies a nonzero cubic
point already over the ground field. -/
theorem exists_rational_lineResidual_point_of_not_irreducible
    (c : Cubic K n) (p d : Vec K n)
    (hp0 : p ≠ 0) (hp : c.eval p = 0) (hdir : c.eval d ≠ 0)
    (hirr : ¬ Irreducible (lineResidualPolynomial c p d)) :
    ∃ x : Vec K n, x ≠ 0 ∧ c.eval x = 0 := by
  let q := lineResidualPolynomial c p d
  have hdegree : q.natDegree = 2 :=
    lineResidualPolynomial_natDegree_eq_two c p d hdir
  obtain ⟨a, ha⟩ := exists_root_of_natDegree_two_of_not_irreducible q hdegree hirr
  let x : Vec K n := p + a • d
  have hroot : Polynomial.eval₂ (RingHom.id K) a q = 0 := by
    change q.eval a = 0
    exact ha
  refine ⟨x, ?_, ?_⟩
  · simpa only [x, RingHom.id_apply] using
      linePoint_ne_zero_of_eval_zero_eval_ne_zero (RingHom.id K) c p d hp0 hp hdir a
  · have hline := eval_linePoint_of_lineResidual_root (RingHom.id K) c p d hp a hroot
    have hmap : c.map (RingHom.id K) = c := by
      funext i
      rfl
    rw [hmap] at hline
    have hpmap : (fun i => (RingHom.id K) (p i)) = p := by
      funext i
      exact RingHom.id_apply _
    have hdmap : (fun i => (RingHom.id K) (d i)) = d := by
      funext i
      exact RingHom.id_apply _
    rw [hpmap, hdmap] at hline
    simpa only [x] using hline

end

end Cubic
end PfaffianDescent
