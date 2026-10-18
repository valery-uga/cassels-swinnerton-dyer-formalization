import AllCharacteristics.KollarSmoothPartialNonzero
import AllCharacteristics.KollarGenericResidualAllFields

/-! The normalized residual discriminant is nonzero for a
smooth cubic in characteristic two over every field, including imperfect
fields. Smoothness supplies the nonzero distinguished derivative; this is
not an assumed separability certificate. All proofs use default heartbeats.
-/

noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory MvPolynomial Polynomial HomogeneousProjective PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Distinguishing the first coordinate converts its multivariate partial
derivative into the ordinary derivative in the distinguished variable. -/
theorem finSuccEquiv_pderiv_zero
    {K : Type u} [CommRing K] (p : MvPolynomial (Fin 4) K) :
    MvPolynomial.finSuccEquiv K 3 (pderiv 0 p) =
      (MvPolynomial.finSuccEquiv K 3 p).derivative := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.finSuccEquiv_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [pderiv_mul, map_add, map_mul, Polynomial.derivative_mul, hp]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [MvPolynomial.finSuccEquiv_X_zero]
      · simp [MvPolynomial.finSuccEquiv_X_succ, pderiv_X,
          Fin.succ_ne_zero]

/-- A polynomial of degree at most two in characteristic two has constant
derivative equal to its linear coefficient. -/
theorem quadratic_derivative_eq_C_linearCoeff_of_two_eq_zero
    {R : Type*} [CommRing R] (f : R[X])
    (hdeg : f.natDegree ≤ 2) (h2 : (2 : R) = 0) :
    f.derivative = Polynomial.C (f.coeff 1) := by
  ext n
  rw [Polynomial.coeff_derivative]
  rcases n with _ | (_ | n)
  · simp
  · simp
    rw [one_add_one_eq_two, h2, mul_zero]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

/-- The normalized cubic's distinguished derivative is nonzero solely from
actual smoothness; no separable-projection premise is present. -/
theorem kollarDistinguishedCoordinatePolynomial_derivative_ne_zero_charTwo
    {K : Type u} [Field K] [CharP K 2]
    (c : Cubic K 4) (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hc0 : c.toMvPolynomial ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)] :
    (kollarDistinguishedCoordinatePolynomial c).derivative ≠ 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3one : (3 : K) = 1 := by linear_combination h2
  have h3 : (3 : K) ≠ 0 := by rw [h3one]; exact one_ne_zero
  have hp := smoothCubic_pderiv_zero_ne_zero_of_three_ne_zero
    c.toMvPolynomial hhom hc0 h3
  intro hzero
  apply hp
  apply (MvPolynomial.finSuccEquiv K 3).injective
  rw [finSuccEquiv_pderiv_zero, map_zero]
  exact hzero

/-- In characteristic two the generic linear coefficient is nonzero for a
normalized nonzero smooth cubic. -/
theorem kollarDistinguishedCoordinatePolynomial_coeff_one_ne_zero_charTwo
    {K : Type u} [Field K] [CharP K 2]
    (c : Cubic K 4) (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hc0 : c.toMvPolynomial ≠ 0)
    (hpoint : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)] :
    (kollarDistinguishedCoordinatePolynomial c).coeff 1 ≠ 0 := by
  have hdegree := kollarDistinguishedCoordinatePolynomial_natDegree_eq_two_allFields
    c hpoint hsec
  have hderiv := kollarDistinguishedCoordinatePolynomial_derivative_ne_zero_charTwo
    c hhom hc0
  intro hzero
  apply hderiv
  rw [quadratic_derivative_eq_C_linearCoeff_of_two_eq_zero _ hdegree.le
    (CharP.cast_eq_zero (KollarProjectiveDirectionRing K) 2), hzero, map_zero]

/-- The generic residual discriminant is nonzero in characteristic two over
an arbitrary field. This closes the inseparable-projection branch of §18 for
smooth cubics without any perfectness assumption. -/
theorem kollarDistinguishedCoordinatePolynomial_discr_ne_zero_charTwo
    {K : Type u} [Field K] [CharP K 2]
    (c : Cubic K 4) (hhom : c.toMvPolynomial.IsHomogeneous 3)
    (hc0 : c.toMvPolynomial ≠ 0)
    (hpoint : c.eval (kollarBasePoint K) = 0)
    (hsec : c.mixed (kollarBasePoint K)
      (kollarAffineLineDirection K (fun _ => 0)) ≠ 0)
    [Smooth (hypersurfaceToBase c.toMvPolynomial hhom)] :
    (kollarDistinguishedCoordinatePolynomial c).discr ≠ 0 := by
  let R := KollarProjectiveDirectionRing K
  let P := kollarDistinguishedCoordinatePolynomial c
  have h2 : (2 : R) = 0 := CharP.cast_eq_zero R 2
  have h4 : (4 : R) = 0 := by
    calc
      (4 : R) = 2 * 2 := by norm_num
      _ = 0 := by rw [h2, mul_zero]
  have hPnat : P.natDegree = 2 :=
    kollarDistinguishedCoordinatePolynomial_natDegree_eq_two_allFields c hpoint hsec
  have hPdegree : P.degree = 2 :=
    (Polynomial.degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 2)).mpr hPnat
  have hlinear : P.coeff 1 ≠ 0 :=
    kollarDistinguishedCoordinatePolynomial_coeff_one_ne_zero_charTwo
      c hhom hc0 hpoint hsec
  rw [Polynomial.discr_of_degree_eq_two hPdegree]
  simpa [h4] using pow_ne_zero 2 hlinear

end AllCharacteristics
