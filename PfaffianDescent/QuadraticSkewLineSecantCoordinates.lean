import PfaffianDescent.QuadraticConjugateDescent
import PfaffianDescent.GaloisFixedPolynomialCoefficientDescent
import Mathlib.Tactic

/-!
SOURCE ONLY. First algebraic lemmas for the genuine birational secant map
of a cubic containing two skew lines. No rationality endpoint is assumed
or declared here. The original smooth cubic must still be converted to
this mixed homogeneous normal form, and the coordinate inverse must be
assembled into an actual isomorphism of dense open schemes.
-/

noncomputable section
namespace PfaffianDescent.QuadraticSkewRationality

open Module MvPolynomial

universe u v

/-- The twelve mixed cubic monomials remaining after a cubic vanishes
scheme-theoretically on the two complementary coordinate lines. -/
structure SplitMixedCubicCoefficients (R : Type u) where
  left : Fin 6 → R
  right : Fin 6 → R

section Ring
variable {R : Type u} [CommRing R]

def leftMixedValue (c : SplitMixedCubicCoefficients R)
    (x₀ x₁ y₀ y₁ : R) : R :=
  x₀ ^ 2 * (c.left 0 * y₀ + c.left 1 * y₁) +
    x₀ * x₁ * (c.left 2 * y₀ + c.left 3 * y₁) +
    x₁ ^ 2 * (c.left 4 * y₀ + c.left 5 * y₁)

def rightMixedValue (c : SplitMixedCubicCoefficients R)
    (x₀ x₁ y₀ y₁ : R) : R :=
  y₀ ^ 2 * (c.right 0 * x₀ + c.right 1 * x₁) +
    y₀ * y₁ * (c.right 2 * x₀ + c.right 3 * x₁) +
    y₁ ^ 2 * (c.right 4 * x₀ + c.right 5 * x₁)

def splitCubicValue (c : SplitMixedCubicCoefficients R)
    (x₀ x₁ y₀ y₁ : R) : R :=
  leftMixedValue c x₀ x₁ y₀ y₁ + rightMixedValue c x₀ x₁ y₀ y₁

/-- The residual equation on each transversal secant is linear after its
two known line-intersection factors are removed. -/
theorem splitCubicValue_secant_factorization
    (c : SplitMixedCubicCoefficients R) (x₀ x₁ y₀ y₁ lam μ : R) :
    splitCubicValue c (lam * x₀) (lam * x₁) (μ * y₀) (μ * y₁) =
      lam * μ * (lam * leftMixedValue c x₀ x₁ y₀ y₁ +
        μ * rightMixedValue c x₀ x₁ y₀ y₁) := by
  simp only [splitCubicValue, leftMixedValue, rightMixedValue]
  ring

def residualCoordinates (c : SplitMixedCubicCoefficients R) (t z : R) : Fin 4 → R :=
  let A := leftMixedValue c 1 t 1 z
  let B := rightMixedValue c 1 t 1 z
  ![B, B * t, -A, -A * z]

/-- The explicitly constructed secant residual lies on the cubic. -/
theorem residualCoordinates_on_cubic
    (c : SplitMixedCubicCoefficients R) (t z : R) :
    splitCubicValue c (residualCoordinates c t z 0)
      (residualCoordinates c t z 1) (residualCoordinates c t z 2)
      (residualCoordinates c t z 3) = 0 := by
  let A := leftMixedValue c 1 t 1 z
  let B := rightMixedValue c 1 t 1 z
  change splitCubicValue c B (B * t) (-A) ((-A) * z) = 0
  calc
    _ = B * (-A) * (B * A + (-A) * B) := by
      simpa only [mul_one] using
        (splitCubicValue_secant_factorization c 1 t 1 z B (-A))
    _ = 0 := by ring

/-- Two conjugate affine-line parameters are the scalar extension of an
affine plane. This determinant identity also works in characteristic two. -/
theorem conjugateParameter_difference (α β T U : R) :
    (T + α * U) - (T + β * U) = (α - β) * U := by
  ring

theorem conjugateParameter_constant (α β T U : R) :
    α * (T + β * U) - β * (T + α * U) = (α - β) * T := by
  ring

/-- Exchanging the two endpoints and their mixed coefficients negates
the residual vector in every ambient coordinate. -/
theorem residualVector_antiInvariant
    {J : Type v} (g : R →+* R) (A B : R) (p q : J → R)
    (hA : g A = B) (hB : g B = A)
    (hp : ∀ i, g (p i) = q i) (hq : ∀ i, g (q i) = p i) :
    ∀ i, g (B * p i - A * q i) = -(B * p i - A * q i) := by
  intro i
  rw [map_sub, map_mul, map_mul, hA, hB, hp i, hq i]
  ring

end Ring

section Field
variable {E : Type u} [Field E]

/-- The two ratios recover the parameters on the secant map's explicit
open domain. These are actual rational inverse formulas, not a point count. -/
theorem residualCoordinates_left_ratio
    (c : SplitMixedCubicCoefficients E) (t z : E)
    (hB : rightMixedValue c 1 t 1 z ≠ 0) :
    residualCoordinates c t z 1 / residualCoordinates c t z 0 = t := by
  dsimp [residualCoordinates]
  field_simp [hB]

theorem residualCoordinates_right_ratio
    (c : SplitMixedCubicCoefficients E) (t z : E)
    (hA : leftMixedValue c 1 t 1 z ≠ 0) :
    residualCoordinates c t z 3 / residualCoordinates c t z 2 = z := by
  dsimp [residualCoordinates]
  field_simp [hA]

theorem residualCoordinates_ne_zero
    (c : SplitMixedCubicCoefficients E) (t z : E)
    (hB : rightMixedValue c 1 t 1 z ≠ 0) :
    residualCoordinates c t z ≠ 0 := by
  intro h
  have h₀ := congrFun h 0
  exact hB (by simpa only [residualCoordinates, Matrix.cons_val_zero,
    Pi.zero_apply] using h₀)

theorem conjugateParameter_inverse_second (α β T U : E) (hαβ : α ≠ β) :
    ((T + α * U) - (T + β * U)) / (α - β) = U := by
  rw [conjugateParameter_difference]
  exact mul_div_cancel_left₀ U (sub_ne_zero.mpr hαβ)

theorem conjugateParameter_inverse_first (α β T U : E) (hαβ : α ≠ β) :
    (α * (T + β * U) - β * (T + α * U)) / (α - β) = T := by
  rw [conjugateParameter_constant]
  exact mul_div_cancel_left₀ T (sub_ne_zero.mpr hαβ)

/-- A cubic point with nonzero first coordinate in each block satisfies
the exact residual linear relation. -/
theorem splitCubicValue_affine_ratio_factorization
    (c : SplitMixedCubicCoefficients E) (x₀ x₁ y₀ y₁ : E)
    (hx₀ : x₀ ≠ 0) (hy₀ : y₀ ≠ 0) :
    splitCubicValue c x₀ x₁ y₀ y₁ =
      x₀ * y₀ *
        (x₀ * leftMixedValue c 1 (x₁ / x₀) 1 (y₁ / y₀) +
          y₀ * rightMixedValue c 1 (x₁ / x₀) 1 (y₁ / y₀)) := by
  simp only [splitCubicValue, leftMixedValue, rightMixedValue]
  field_simp [hx₀, hy₀] <;> ring

theorem splitCubicValue_affine_ratio_relation
    (c : SplitMixedCubicCoefficients E) (x₀ x₁ y₀ y₁ : E)
    (hx₀ : x₀ ≠ 0) (hy₀ : y₀ ≠ 0)
    (hF : splitCubicValue c x₀ x₁ y₀ y₁ = 0) :
    x₀ * leftMixedValue c 1 (x₁ / x₀) 1 (y₁ / y₀) +
      y₀ * rightMixedValue c 1 (x₁ / x₀) 1 (y₁ / y₀) = 0 := by
  have h := (splitCubicValue_affine_ratio_factorization c x₀ x₁ y₀ y₁ hx₀ hy₀).symm.trans hF
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hx₀ hy₀)

/-- Conversely the residual vector recovers the original homogeneous
point up to an explicit nonzero scalar on the chosen open chart. -/
theorem residual_vector_reconstruction
    (A B x₀ x₁ y₀ y₁ : E) (hx₀ : x₀ ≠ 0) (hy₀ : y₀ ≠ 0)
    (hrel : x₀ * A + y₀ * B = 0) :
    ![B, B * (x₁ / x₀), -A, -A * (y₁ / y₀)] =
      (B / x₀) • ![x₀, x₁, y₀, y₁] := by
  have hAy : -A = (B / x₀) * y₀ := by
    field_simp [hx₀] <;> linear_combination -hrel
  ext i
  fin_cases i
  · change B = (B / x₀) * x₀
    field_simp [hx₀]
  · change B * (x₁ / x₀) = (B / x₀) * x₁
    field_simp [hx₀] <;> ring
  · change -A = (B / x₀) * y₀
    exact hAy
  · change -A * (y₁ / y₀) = (B / x₀) * y₁
    rw [hAy]
    field_simp [hy₀] <;> ring

theorem residualCoordinates_recover_point
    (c : SplitMixedCubicCoefficients E) (x₀ x₁ y₀ y₁ : E)
    (hx₀ : x₀ ≠ 0) (hy₀ : y₀ ≠ 0)
    (hF : splitCubicValue c x₀ x₁ y₀ y₁ = 0) :
    residualCoordinates c (x₁ / x₀) (y₁ / y₀) =
      (rightMixedValue c 1 (x₁ / x₀) 1 (y₁ / y₀) / x₀) •
        ![x₀, x₁, y₀, y₁] := by
  exact residual_vector_reconstruction _ _ _ _ _ _ hx₀ hy₀
    (splitCubicValue_affine_ratio_relation c x₀ x₁ y₀ y₁ hx₀ hy₀ hF)

end Field

section PolynomialDescent
variable {k E : Type u} [Field k] [Field E] [Algebra k E]
  [FiniteDimensional k E] [IsGalois k E]

/-- Fixedness under the single nonidentity quadratic automorphism suffices
to descend each polynomial. The Galois coverage is derived from degree2. -/
theorem quadratic_fixed_polynomial_descends
    {J : Type v} (σ : E ≃ₐ[k] E) (hσ : σ ≠ AlgEquiv.refl)
    (h₂ : finrank k E = 2) (q : MvPolynomial J E)
    (hfixed : MvPolynomial.map σ.toRingHom q = q) :
    ∃ Q : MvPolynomial J k, MvPolynomial.map (algebraMap k E) Q = q := by
  apply galois_fixed_polynomial_descends q
  intro g
  rcases galois_aut_eq_refl_or_of_finrank_two σ hσ h₂ g with hg | hg
  · subst g
    change MvPolynomial.map (RingHom.id E) q = q
    exact MvPolynomial.map_id q
  · subst g
    exact hfixed

/-- The whole varying secant residual, expressed in the original ground
ambient coordinates, descends coefficientwise. The exchange hypotheses
are algebraic identities to be derived from the original cubic and a
conjugate frame; this theorem assumes no birationality certificate. -/
theorem conjugate_residual_polynomial_coordinates_descend
    {J : Type v} {I : Type u} (σ : E ≃ₐ[k] E)
    (hσ : σ ≠ AlgEquiv.refl) (h₂ : finrank k E = 2)
    (A B : MvPolynomial J E) (p q : I → MvPolynomial J E)
    (hA : MvPolynomial.map σ.toRingHom A = B)
    (hB : MvPolynomial.map σ.toRingHom B = A)
    (hp : ∀ i, MvPolynomial.map σ.toRingHom (p i) = q i)
    (hq : ∀ i, MvPolynomial.map σ.toRingHom (q i) = p i) :
    ∃ δ : E, δ ≠ 0 ∧ ∃ r : I → MvPolynomial J k,
      ∀ i, MvPolynomial.map (algebraMap k E) (r i) =
        MvPolynomial.C δ * (B * p i - A * q i) := by
  obtain ⟨δ, hδ₀, hδ⟩ := exists_nonzero_antiInvariant_of_involution σ
    (galois_involution_of_finrank_two σ hσ h₂) hσ
  have hfixed (i : I) : MvPolynomial.map σ.toRingHom
      (MvPolynomial.C δ * (B * p i - A * q i)) =
        MvPolynomial.C δ * (B * p i - A * q i) := by
    have hδmap : σ.toRingHom δ = -δ := hδ
    rw [map_mul, MvPolynomial.map_C, hδmap,
      residualVector_antiInvariant (MvPolynomial.map σ.toRingHom) A B p q hA hB hp hq i]
    simp only [map_neg, neg_mul_neg]
  choose r hr using fun i => quadratic_fixed_polynomial_descends σ hσ h₂
    (MvPolynomial.C δ * (B * p i - A * q i)) (hfixed i)
  exact ⟨δ, hδ₀, r, hr⟩

end PolynomialDescent

end PfaffianDescent.QuadraticSkewRationality

