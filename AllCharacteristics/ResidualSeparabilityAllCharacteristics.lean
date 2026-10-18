import PfaffianDescent.CubicLineResidualTransversality

/-!
# Residual-line separability without a characteristic-zero assumption

This file proves the exact coefficient obstruction in the quadratic-pair
construction.  It does not assert dominance or unirationality.  In particular,
the characteristic-two case is retained rather than hidden in a characteristic
zero separability invocation.
-/

namespace PfaffianDescent.Cubic

open Polynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- The linear residual coefficient is the constant derivative coefficient. -/
theorem lineResidualPolynomial_derivative_coeff_zero
    (c : Cubic K n) (p d : Vec K n) :
    (lineResidualPolynomial c p d).derivative.coeff 0 = c.mixed d p := by
  simp [Polynomial.coeff_derivative, lineResidualPolynomial]

/-- The other derivative coefficient is twice the leading residual coefficient. -/
theorem lineResidualPolynomial_derivative_coeff_one
    (c : Cubic K n) (p d : Vec K n) :
    (lineResidualPolynomial c p d).derivative.coeff 1 =
      (2 : K) * c.eval d := by
  rw [Polynomial.coeff_derivative]
  norm_num only [Nat.reduceAdd, Cubic.lineResidualPolynomial_coeff_two, Nat.cast_ofNat]
  exact mul_comm _ _

/-- The derivative of the residual quadratic, in all characteristics. -/
theorem lineResidualPolynomial_derivative_eq
    (c : Cubic K n) (p d : Vec K n) :
    (lineResidualPolynomial c p d).derivative =
      C (c.mixed d p) + C ((2 : K) * c.eval d) * X := by
  simp [lineResidualPolynomial, Polynomial.derivative_mul,
    Polynomial.derivative_pow]
  ring

/-- An irreducible genuine residual quadratic is separable precisely when
either its linear coefficient is nonzero or the characteristic is not two. -/
theorem lineResidualPolynomial_separable_iff
    (c : Cubic K n) (p d : Vec K n)
    (hdir : c.eval d ≠ 0)
    (hirr : Irreducible (lineResidualPolynomial c p d)) :
    (lineResidualPolynomial c p d).Separable ↔
      c.mixed d p ≠ 0 ∨ (2 : K) ≠ 0 := by
  rw [Polynomial.separable_iff_derivative_ne_zero hirr]
  constructor
  · intro hder
    by_contra h
    push Not at h
    apply hder
    rw [lineResidualPolynomial_derivative_eq, h.1, h.2]
    simp
  · rintro (hlinear | htwo) hder
    · apply hlinear
      have h := congrArg (fun q : K[X] => q.coeff 0) hder
      simpa only [lineResidualPolynomial_derivative_coeff_zero,
        Polynomial.coeff_zero] using h
    · have h := congrArg (fun q : K[X] => q.coeff 1) hder
      have hprod : (2 : K) * c.eval d = 0 := by
        simpa only [lineResidualPolynomial_derivative_coeff_one,
          Polynomial.coeff_zero] using h
      exact mul_ne_zero htwo hdir hprod

/-- Separability, rather than characteristic zero, is the actual hypothesis
needed for transverse residual intersections after arbitrary field extension. -/
theorem mixed_distinct_linePoints_ne_zero_of_separable
    {L : Type u} [Field L] {f : K →+* L}
    (c : Cubic K n) (p d : Vec K n)
    (hp : c.eval p = 0) (hsec : c.mixed p d ≠ 0)
    (hsep : (lineResidualPolynomial c p d).Separable)
    (a b : L) (hab : a ≠ b)
    (hroot : Polynomial.eval₂ f b (lineResidualPolynomial c p d) = 0) :
    (c.map f).mixed
      ((fun i => f (p i)) + b • (fun i => f (d i)))
      ((fun i => f (p i)) + a • (fun i => f (d i))) ≠ 0 := by
  let q := lineResidualPolynomial c p d
  let cL := c.map f
  let pL : Vec L n := fun i => f (p i)
  let dL : Vec L n := fun i => f (d i)
  have hqL : Polynomial.map f q = lineResidualPolynomial cL pL dL :=
    map_lineResidualPolynomial f c p d
  have hy : cL.eval (pL + b • dL) = 0 :=
    eval_linePoint_of_lineResidual_root f c p d hp b hroot
  have hb : b ≠ 0 :=
    lineResidual_root_ne_zero_of_mixed_ne_zero f c p d hsec b hroot
  apply mixed_distinct_linePoints_ne_zero_of_simple_residual_root
    cL pL dL a b hab hy hb
  · rw [← hqL, Polynomial.eval_map]
    exact hroot
  · have hsimple := hsep.eval₂_derivative_ne_zero f hroot
    rw [← hqL, Polynomial.derivative_map, Polynomial.eval_map]
    exact hsimple

/-- The two conjugate line-residual points avoid each other's tangent planes
over any field when the residual polynomial is separable. -/
theorem mixed_conjugate_lineResidual_points_ne_zero_of_separable
    (c : Cubic K n) (p d : Vec K n)
    (hp : c.eval p = 0) (hsec : c.mixed p d ≠ 0)
    (hirr : Irreducible (lineResidualPolynomial c p d))
    (hsep : (lineResidualPolynomial c p d).Separable)
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
    exact (adjoinRoot_root_ne_of_algEquiv_ne_refl q σ hσ).symm
  have hroot : Polynomial.eval₂ (algebraMap K (AdjoinRoot q)) (σ a) q = 0 :=
    eval₂_adjoinRoot_root_apply_algEquiv q σ
  simpa only [q, a] using
    (mixed_distinct_linePoints_ne_zero_of_separable
      c p d hp hsec hsep a (σ a) hdiff hroot)

end PfaffianDescent.Cubic
