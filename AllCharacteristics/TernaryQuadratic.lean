import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/-!
# Ternary quadratics and the double-point construction

This is the characteristic-free coefficient calculation used in the paper's
replacement of a double point by a smooth point.  It is deliberately stated
without an infinitude assumption on the field.
-/

namespace AllCharacteristics

/-- The six coefficients of a ternary homogeneous quadratic. -/
structure TernaryQuadratic (K : Type*) where
  q00 : K
  q11 : K
  q22 : K
  q01 : K
  q02 : K
  q12 : K

instance {K : Type*} [Zero K] : Zero (TernaryQuadratic K) where
  zero := ⟨0, 0, 0, 0, 0, 0⟩

namespace TernaryQuadratic
variable {K : Type*} [Field K]

/-- The multivariate polynomial represented by the six coefficients. -/
noncomputable def toMvPolynomial (Q : TernaryQuadratic K) : MvPolynomial (Fin 3) K :=
  MvPolynomial.C Q.q00 * MvPolynomial.X 0 ^ 2 +
    MvPolynomial.C Q.q11 * MvPolynomial.X 1 ^ 2 +
    MvPolynomial.C Q.q22 * MvPolynomial.X 2 ^ 2 +
    MvPolynomial.C Q.q01 * MvPolynomial.X 0 * MvPolynomial.X 1 +
    MvPolynomial.C Q.q02 * MvPolynomial.X 0 * MvPolynomial.X 2 +
    MvPolynomial.C Q.q12 * MvPolynomial.X 1 * MvPolynomial.X 2

/-- Evaluation of a ternary quadratic in the standard monomial basis. -/
def eval (Q : TernaryQuadratic K) (a : Fin 3 → K) : K :=
  Q.q00 * a 0 ^ 2 + Q.q11 * a 1 ^ 2 + Q.q22 * a 2 ^ 2 +
    Q.q01 * a 0 * a 1 + Q.q02 * a 0 * a 2 + Q.q12 * a 1 * a 2

@[simp] theorem eval_toMvPolynomial (Q : TernaryQuadratic K) (a : Fin 3 → K) :
    MvPolynomial.eval a Q.toMvPolynomial = Q.eval a := by
  simp [toMvPolynomial, eval]

/-- The coefficient polynomial is homogeneous of degree two. -/
theorem toMvPolynomial_isHomogeneous (Q : TernaryQuadratic K) :
    Q.toMvPolynomial.IsHomogeneous 2 := by
  have h00 := MvPolynomial.isHomogeneous_C_mul_X_pow Q.q00 (0 : Fin 3) 2
  have h11 := MvPolynomial.isHomogeneous_C_mul_X_pow Q.q11 (1 : Fin 3) 2
  have h22 := MvPolynomial.isHomogeneous_C_mul_X_pow Q.q22 (2 : Fin 3) 2
  have h01 : (MvPolynomial.C Q.q01 * MvPolynomial.X (0 : Fin 3) *
      MvPolynomial.X 1).IsHomogeneous 2 := by
    simpa using (MvPolynomial.isHomogeneous_C_mul_X Q.q01 (0 : Fin 3)).mul
      (MvPolynomial.isHomogeneous_X K (1 : Fin 3))
  have h02 : (MvPolynomial.C Q.q02 * MvPolynomial.X (0 : Fin 3) *
      MvPolynomial.X 2).IsHomogeneous 2 := by
    simpa using (MvPolynomial.isHomogeneous_C_mul_X Q.q02 (0 : Fin 3)).mul
      (MvPolynomial.isHomogeneous_X K (2 : Fin 3))
  have h12 : (MvPolynomial.C Q.q12 * MvPolynomial.X (1 : Fin 3) *
      MvPolynomial.X 2).IsHomogeneous 2 := by
    simpa using (MvPolynomial.isHomogeneous_C_mul_X Q.q12 (1 : Fin 3)).mul
      (MvPolynomial.isHomogeneous_X K (2 : Fin 3))
  simpa only [toMvPolynomial, add_assoc] using
    h00.add (h11.add (h22.add (h01.add (h02.add h12))))

@[simp] theorem eval_zero (Q : TernaryQuadratic K) : Q.eval 0 = 0 := by
  simp [eval]

/-- A nonzero ternary quadratic has a nonzero value over every field,
including `𝔽₂`.  The proof recovers square coefficients at the basis vectors
and cross coefficients at sums of two basis vectors. -/
theorem exists_eval_ne_zero (Q : TernaryQuadratic K) (hQ : Q ≠ 0) :
    ∃ a : Fin 3 → K, Q.eval a ≠ 0 := by
  by_cases h00 : Q.q00 = 0
  · by_cases h11 : Q.q11 = 0
    · by_cases h22 : Q.q22 = 0
      · by_cases h01 : Q.q01 = 0
        · by_cases h02 : Q.q02 = 0
          · have h12 : Q.q12 ≠ 0 := by
              intro h12
              apply hQ
              cases Q
              congr
            refine ⟨![0, 1, 1], ?_⟩
            simpa [eval, h00, h11, h22, h01, h02] using h12
          · refine ⟨![1, 0, 1], ?_⟩
            simpa [eval, h00, h11, h22, h01] using h02
        · refine ⟨![1, 1, 0], ?_⟩
          simpa [eval, h00, h11, h22] using h01
      · refine ⟨![0, 0, 1], ?_⟩
        simpa [eval, h00, h11] using h22
    · refine ⟨![0, 1, 0], ?_⟩
      simpa [eval, h00] using h11
  · refine ⟨![1, 0, 0], ?_⟩
    simpa [eval] using h00

/-- The homogeneous coordinate vector with first coordinate `u` and tail `a`. -/
def point (u : K) (a : Fin 3 → K) : Fin 4 → K := Fin.cases u a

theorem point_ne_zero_of_tail_ne_zero (u : K) {a : Fin 3 → K} (ha : a ≠ 0) :
    point u a ≠ 0 := by
  intro h
  apply ha
  funext i
  have hi := congrFun h i.succ
  simpa [point] using hi

/-- The equation `x₀ Q(a) + C(a)` attached to the double-point normal form. -/
def doublePointValue (Q : TernaryQuadratic K) (C : (Fin 3 → K) → K)
    (u : K) (a : Fin 3 → K) : K :=
  u * Q.eval a + C a

/-- Projection from a double point produces a second point, and the partial
derivative in the `x₀` direction there is nonzero. -/
theorem exists_doublePointValue_zero_with_nonzero_x0Derivative
    (Q : TernaryQuadratic K) (hQ : Q ≠ 0) (C : (Fin 3 → K) → K) :
    ∃ u : K, ∃ a : Fin 3 → K,
      point u a ≠ 0 ∧ doublePointValue Q C u a = 0 ∧ Q.eval a ≠ 0 := by
  obtain ⟨a, haQ⟩ := Q.exists_eval_ne_zero hQ
  have ha : a ≠ 0 := by
    intro ha
    subst a
    exact haQ Q.eval_zero
  refine ⟨-(C a / Q.eval a), a, point_ne_zero_of_tail_ne_zero _ ha, ?_, haQ⟩
  dsimp [doublePointValue]
  field_simp
  simp

end TernaryQuadratic
end AllCharacteristics
