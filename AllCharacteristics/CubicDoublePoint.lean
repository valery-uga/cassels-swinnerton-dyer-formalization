import AllCharacteristics.TernaryQuadratic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The cubic double-point normal form

This file connects the finite-field-safe ternary quadratic calculation to the
actual four-variable equation `x₀ Q + C` used in the paper.
-/

namespace AllCharacteristics
namespace TernaryQuadratic

variable {K : Type*} [Field K]

/-- Regard a polynomial in the last three variables as a polynomial in four
variables. -/
noncomputable def tailPolynomial (r : MvPolynomial (Fin 3) K) :
    MvPolynomial (Fin 4) K := MvPolynomial.rename Fin.succ r

@[simp] theorem tailPolynomial_add (p q : MvPolynomial (Fin 3) K) :
    tailPolynomial (p + q) = tailPolynomial p + tailPolynomial q := by
  simp [tailPolynomial]

@[simp] theorem tailPolynomial_mul_X (p : MvPolynomial (Fin 3) K) (i : Fin 3) :
    tailPolynomial (p * MvPolynomial.X i) =
      tailPolynomial p * MvPolynomial.X i.succ := by
  simp [tailPolynomial]

/-- The four-variable cubic normal form at a double point. -/
noncomputable def doublePointPolynomial (Q : TernaryQuadratic K)
    (C : MvPolynomial (Fin 3) K) : MvPolynomial (Fin 4) K :=
  MvPolynomial.X 0 * tailPolynomial Q.toMvPolynomial + tailPolynomial C

/-- Renaming the tail variables preserves homogeneity. -/
theorem tailPolynomial_isHomogeneous {r : MvPolynomial (Fin 3) K} {d : ℕ}
    (hr : r.IsHomogeneous d) : (tailPolynomial r).IsHomogeneous d := by
  exact hr.rename_isHomogeneous

/-- The normal form is a homogeneous cubic when its tail is cubic. -/
theorem doublePointPolynomial_isHomogeneous (Q : TernaryQuadratic K)
    (C : MvPolynomial (Fin 3) K) (hC : C.IsHomogeneous 3) :
    (doublePointPolynomial Q C).IsHomogeneous 3 := by
  have hQ : (tailPolynomial Q.toMvPolynomial).IsHomogeneous 2 :=
    tailPolynomial_isHomogeneous Q.toMvPolynomial_isHomogeneous
  have hxQ : (MvPolynomial.X (0 : Fin 4) *
      tailPolynomial Q.toMvPolynomial).IsHomogeneous 3 := by
    simpa using (MvPolynomial.isHomogeneous_X K (0 : Fin 4)).mul hQ
  exact hxQ.add (tailPolynomial_isHomogeneous hC)

@[simp] theorem eval_tailPolynomial (r : MvPolynomial (Fin 3) K)
    (u : K) (a : Fin 3 → K) :
    MvPolynomial.eval (point u a) (tailPolynomial r) = MvPolynomial.eval a r := by
  rw [tailPolynomial, MvPolynomial.eval_rename]
  congr 1

@[simp] theorem eval_doublePointPolynomial (Q : TernaryQuadratic K)
    (C : MvPolynomial (Fin 3) K) (u : K) (a : Fin 3 → K) :
    MvPolynomial.eval (point u a) (doublePointPolynomial Q C) =
      doublePointValue Q (MvPolynomial.eval · C) u a := by
  simp [doublePointPolynomial, doublePointValue, point]

/-- A renamed tail polynomial has zero `x₀` derivative. -/
theorem pderiv_zero_tailPolynomial (r : MvPolynomial (Fin 3) K) :
    MvPolynomial.pderiv 0 (tailPolynomial r) = 0 := by
  classical
  induction r using MvPolynomial.induction_on with
  | C c => simp [tailPolynomial]
  | add p q hp hq =>
      rw [tailPolynomial_add, map_add, hp, hq, add_zero]
  | mul_X p i hp =>
      rw [tailPolynomial_mul_X, Derivation.leibniz, hp]
      simp

/-- The `x₀` partial derivative of `x₀ Q + C` is exactly `Q`. -/
theorem pderiv_zero_doublePointPolynomial (Q : TernaryQuadratic K)
    (C : MvPolynomial (Fin 3) K) :
    MvPolynomial.pderiv 0 (doublePointPolynomial Q C) =
      tailPolynomial Q.toMvPolynomial := by
  simp [doublePointPolynomial, pderiv_zero_tailPolynomial]

/-- The coordinate projection construction produces a nonzero point of the
actual cubic normal form at which the `x₀` partial derivative is nonzero. -/
theorem exists_point_doublePointPolynomial_with_nonzero_pderiv
    (Q : TernaryQuadratic K) (hQ : Q ≠ 0)
    (C : MvPolynomial (Fin 3) K) :
    ∃ x : Fin 4 → K, x ≠ 0 ∧
      MvPolynomial.eval x (doublePointPolynomial Q C) = 0 ∧
      MvPolynomial.eval x
        (MvPolynomial.pderiv 0 (doublePointPolynomial Q C)) ≠ 0 := by
  obtain ⟨u, a, hx, heval, hderiv⟩ :=
    exists_doublePointValue_zero_with_nonzero_x0Derivative
      Q hQ (MvPolynomial.eval · C)
  refine ⟨point u a, hx, ?_, ?_⟩
  · simpa using heval
  · rw [pderiv_zero_doublePointPolynomial]
    simpa using hderiv

end TernaryQuadratic
end AllCharacteristics
