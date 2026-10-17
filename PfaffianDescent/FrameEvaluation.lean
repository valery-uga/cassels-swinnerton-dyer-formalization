import PfaffianDescent.FrameCoordinateRing
import Mathlib.Algebra.Algebra.Pi

namespace PfaffianDescent
open Polynomial
open scoped BigOperators

section
variable {K : Type*} [Field K]

/-- Homogeneous evaluation on the four coordinate axes and the diagonal line. -/
noncomputable def frameLineVariable (p : Option (Fin 4)) (i : Fin 4) : K[X] :=
  match p with
  | none => X
  | some j => if i = j then X else 0

theorem frameLineVariable_mixed (p : Option (Fin 4)) (i j : Fin 4) (hij : i ≠ j) :
    frameLineVariable (K := K) p i * frameLineVariable p j =
      if p = none then X ^ 2 else 0 := by
  cases p with
  | none => simp only [frameLineVariable, ↓reduceIte, pow_two]
  | some k =>
      simp only [frameLineVariable, reduceCtorEq, ↓reduceIte]
      by_cases hi : i = k
      · have hj : j ≠ k := fun h => hij (hi.trans h.symm)
        simp only [hi, hj, ↓reduceIte, mul_zero]
      · simp only [hi, ↓reduceIte, zero_mul]

private theorem mixedRelation_line_vanish (p : Option (Fin 4)) (i j : Fin 4) (hij : i ≠ j) :
    MvPolynomial.aeval (frameLineVariable (K := K) p)
      (MvPolynomial.X i * MvPolynomial.X j - MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 4) K) = 0 := by
  rw [map_sub, map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
    MvPolynomial.aeval_X, MvPolynomial.aeval_X,
    frameLineVariable_mixed p i j hij, frameLineVariable_mixed p 0 1 (by decide), sub_self]

private theorem frameRelations_line_vanish (p : Option (Fin 4)) (i : Fin 5) :
    MvPolynomial.aeval (frameLineVariable (K := K) p) (frameRelations (K := K) i) = 0 := by
  fin_cases i
  · exact mixedRelation_line_vanish p 0 2 (by decide)
  · exact mixedRelation_line_vanish p 0 3 (by decide)
  · exact mixedRelation_line_vanish p 1 2 (by decide)
  · exact mixedRelation_line_vanish p 1 3 (by decide)
  · exact mixedRelation_line_vanish p 2 3 (by decide)

namespace FrameCoordinateRing

noncomputable def atLine (p : Option (Fin 4)) : FrameCoordinateRing K →ₐ[K] K[X] :=
  Ideal.Quotient.liftₐ frameIdeal (MvPolynomial.aeval (frameLineVariable p)) (by
    have hle : frameIdeal (K := K) ≤
        RingHom.ker (MvPolynomial.aeval (frameLineVariable (K := K) p)).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact frameRelations_line_vanish p i
    intro a ha
    exact hle ha)

theorem atLine_x (p : Option (Fin 4)) (i : Fin 4) :
    atLine (K := K) p (x i) = frameLineVariable p i := by
  change MvPolynomial.aeval (frameLineVariable (K := K) p) (MvPolynomial.X i) = _
  exact MvPolynomial.aeval_X _ _

theorem atLine_q (p : Option (Fin 4)) :
    atLine (K := K) p q = if p = none then X ^ 2 else 0 := by
  rw [q, map_mul, atLine_x, atLine_x]
  exact frameLineVariable_mixed p 0 1 (by decide)

/-- Polynomial-valued evaluation on all five frame points, retaining the grading. -/
noncomputable def lineEvaluation : FrameCoordinateRing K →ₐ[K] (Option (Fin 4) → K[X]) :=
  AlgHom.pi atLine

end FrameCoordinateRing
end
end PfaffianDescent
