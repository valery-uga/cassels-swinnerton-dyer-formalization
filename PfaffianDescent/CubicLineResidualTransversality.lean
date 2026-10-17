import PfaffianDescent.CubicLineResidualConjugate
import PfaffianDescent.CubicSecant

/-!
# Transversality of residual points on a cubic line

The tangent coefficient at a residual point is the derivative of the
residual line polynomial, multiplied by the residual parameter.  This is the
coordinate form of the transverse-intersection condition used in the
two-conjugate-tangent construction.
-/

namespace PfaffianDescent
namespace Cubic

open Polynomial

universe u

variable {R : Type*} [CommRing R] {n : ℕ}

/-- Along a line through a cubic point, the tangent coefficient at parameter
`b` is the value of the residual quadratic plus `b` times its derivative. -/
theorem mixed_linePoint_direction_eq_residual_derivative
    (c : Cubic R n) (p d : Vec R n) (b : R) :
    c.mixed (p + b • d) d =
      Polynomial.eval b (lineResidualPolynomial c p d) + b *
        Polynomial.eval b (lineResidualPolynomial c p d).derivative := by
  simp only [lineResidualPolynomial, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_pow,
    Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.derivative_pow,
    Polynomial.eval_zero, Polynomial.eval_one,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, mixed, eval]
  simp only [zero_add, zero_mul, mul_one, pow_one, Nat.reduceSubDiff]
  simp only [Finset.sum_mul]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- At a root of the residual polynomial, the tangent coefficient in the
line direction is the parameter times the derivative of that polynomial. -/
theorem mixed_linePoint_direction_eq_mul_residual_derivative_of_root
    (c : Cubic R n) (p d : Vec R n) (b : R)
    (hroot : Polynomial.eval b (lineResidualPolynomial c p d) = 0) :
    c.mixed (p + b • d) d = b *
      Polynomial.eval b (lineResidualPolynomial c p d).derivative := by
  rw [mixed_linePoint_direction_eq_residual_derivative, hroot, zero_add]

/-- The two points at parameters `a` and `b` on a cubic line have tangent
coefficient equal to their parameter difference times the tangent coefficient
of the second point in the line direction. -/
theorem mixed_linePoints_eq_sub_mul_of_linePoint_eval_zero
    (c : Cubic R n) (p d : Vec R n) (a b : R)
    (hb : c.eval (p + b • d) = 0) :
    c.mixed (p + b • d) (p + a • d) =
      (a - b) * c.mixed (p + b • d) d := by
  have hline : p + a • d = (p + b • d) + (a - b) • d := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hline, mixed_add_right, mixed_smul_right, mixed_self_eq_three_eval,
    hb, mul_zero, zero_add]

section

variable {K : Type u} [Field K]

/-- A nonzero simple residual root is transverse to the original line. -/
theorem mixed_linePoint_direction_ne_zero_of_simple_residual_root
    (c : Cubic K n) (p d : Vec K n) (b : K)
    (hb : b ≠ 0)
    (hroot : Polynomial.eval b (lineResidualPolynomial c p d) = 0)
    (hsimple : Polynomial.eval b (lineResidualPolynomial c p d).derivative ≠ 0) :
    c.mixed (p + b • d) d ≠ 0 := by
  rw [mixed_linePoint_direction_eq_mul_residual_derivative_of_root c p d b hroot]
  exact mul_ne_zero hb hsimple

/-- Distinct simple residual roots of a cubic line are not contained in each
other's tangent hyperplanes. -/
theorem mixed_distinct_linePoints_ne_zero_of_simple_residual_root
    (c : Cubic K n) (p d : Vec K n) (a b : K)
    (hab : a ≠ b)
    (hy : c.eval (p + b • d) = 0)
    (hb : b ≠ 0)
    (hroot : Polynomial.eval b (lineResidualPolynomial c p d) = 0)
    (hsimple : Polynomial.eval b (lineResidualPolynomial c p d).derivative ≠ 0) :
    c.mixed (p + b • d) (p + a • d) ≠ 0 := by
  rw [mixed_linePoints_eq_sub_mul_of_linePoint_eval_zero c p d a b hy]
  exact mul_ne_zero (sub_ne_zero.mpr hab)
    (mixed_linePoint_direction_ne_zero_of_simple_residual_root c p d b hb hroot hsimple)

/-- Over characteristic zero, distinct roots of an irreducible residual
quadratic give points which avoid one another's tangent hyperplanes.  The
nonzero parameter and simple-root conditions follow from the residual line
itself. -/
theorem mixed_distinct_linePoints_ne_zero_of_irreducible_charZero
    {L : Type u} [Field L] {f : K →+* L}
    [CharZero K] (c : Cubic K n) (p d : Vec K n)
    (hp : c.eval p = 0) (hsec : c.mixed p d ≠ 0)
    (hirr : Irreducible (lineResidualPolynomial c p d))
    (a b : L) (hab : a ≠ b)
    (hroot : Polynomial.eval₂ f b (lineResidualPolynomial c p d) = 0) :
    (c.map f).mixed
      ((fun i => f (p i)) + b • (fun i => f (d i)))
      ((fun i => f (p i)) + a • (fun i => f (d i))) ≠ 0 := by
  let q := lineResidualPolynomial c p d
  let cL := c.map f
  let pL : Vec L n := fun i => f (p i)
  let dL : Vec L n := fun i => f (d i)
  have hqL : Polynomial.map f q = lineResidualPolynomial cL pL dL := by
    exact map_lineResidualPolynomial f c p d
  have hy : cL.eval (pL + b • dL) = 0 := by
    exact eval_linePoint_of_lineResidual_root f c p d hp b hroot
  have hb : b ≠ 0 :=
    lineResidual_root_ne_zero_of_mixed_ne_zero f c p d hsec b hroot
  apply mixed_distinct_linePoints_ne_zero_of_simple_residual_root
    cL pL dL a b hab hy hb
  · rw [← hqL, Polynomial.eval_map]
    exact hroot
  · have hsimple := hirr.separable.eval₂_derivative_ne_zero f hroot
    rw [← hqL, Polynomial.derivative_map, Polynomial.eval_map]
    exact hsimple

/-- The two distinct conjugate roots of an irreducible residual polynomial in
characteristic zero lie outside one another's tangent hyperplanes.  This
discharges the tangent-plane separation condition in Kollár's two-curve
construction directly from the residual line. -/
theorem mixed_conjugate_lineResidual_points_ne_zero_of_charZero
    [CharZero K] (c : Cubic K n) (p d : Vec K n)
    (hp : c.eval p = 0) (hsec : c.mixed p d ≠ 0)
    (hirr : Irreducible (lineResidualPolynomial c p d))
    (σ : AdjoinRoot (lineResidualPolynomial c p d) ≃ₐ[K]
      AdjoinRoot (lineResidualPolynomial c p d))
    (hσ : σ ≠ AlgEquiv.refl) :
    (c.map (algebraMap K (AdjoinRoot (lineResidualPolynomial c p d)))).mixed
      ((fun i => algebraMap K (AdjoinRoot (lineResidualPolynomial c p d)) (p i)) +
        (σ (AdjoinRoot.root (lineResidualPolynomial c p d))) •
          (fun i => algebraMap K (AdjoinRoot (lineResidualPolynomial c p d)) (d i)))
      ((fun i => algebraMap K (AdjoinRoot (lineResidualPolynomial c p d)) (p i)) +
        (AdjoinRoot.root (lineResidualPolynomial c p d)) •
          (fun i => algebraMap K (AdjoinRoot (lineResidualPolynomial c p d)) (d i))) ≠ 0 := by
  let q := lineResidualPolynomial c p d
  letI : Fact (Irreducible q) := ⟨hirr⟩
  let a : AdjoinRoot q := AdjoinRoot.root q
  have hdiff : a ≠ σ a := by
    change AdjoinRoot.root q ≠ σ (AdjoinRoot.root q)
    exact (adjoinRoot_root_ne_of_algEquiv_ne_refl q σ hσ).symm
  have hroot : Polynomial.eval₂ (algebraMap K (AdjoinRoot q)) (σ a) q = 0 := by
    exact eval₂_adjoinRoot_root_apply_algEquiv q σ
  simpa only [q, a] using
    (mixed_distinct_linePoints_ne_zero_of_irreducible_charZero
      c p d hp hsec hirr a (σ a) hdiff hroot)

end

end Cubic
end PfaffianDescent
