import PfaffianDescent.RelativeHomogeneousTripleIntersectionFamily
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
Correcting a fixed homogeneous equation by an invertible interpolation frame.
The correction vanishes at every marked point, and specializes back to the
original equation wherever that original equation already vanishes. This
constructs relative cubic equations without choosing a full kernel basis.
-/

namespace PfaffianDescent

open MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

noncomputable def homogeneousFrameEvaluationMatrix
    (frame : Fin n → MvPolynomial (Fin 4) R) (x : Fin n → Fin 4 → R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => (frame j).eval (x i)

noncomputable def homogeneousInterpolationCoefficients
    (frame : Fin n → MvPolynomial (Fin 4) R) (x : Fin n → Fin 4 → R)
    (q : MvPolynomial (Fin 4) R) : Fin n → R :=
  Matrix.mulVec (homogeneousFrameEvaluationMatrix frame x)⁻¹ (fun i => q.eval (x i))

noncomputable def homogeneousInterpolationCorrection
    (frame : Fin n → MvPolynomial (Fin 4) R) (x : Fin n → Fin 4 → R)
    (q : MvPolynomial (Fin 4) R) : MvPolynomial (Fin 4) R :=
  q - ∑ j, C (homogeneousInterpolationCoefficients frame x q j) * frame j

theorem homogeneousInterpolationCorrection_isHomogeneous
    (frame : Fin n → MvPolynomial (Fin 4) R) (x : Fin n → Fin 4 → R)
    (q : MvPolynomial (Fin 4) R) {d : ℕ}
    (hframe : ∀ j, (frame j).IsHomogeneous d) (hq : q.IsHomogeneous d) :
    (homogeneousInterpolationCorrection frame x q).IsHomogeneous d := by
  apply hq.sub
  apply IsHomogeneous.sum
  intro j _
  exact (hframe j).C_mul _

theorem homogeneousInterpolationCorrection_eval_zero
    (frame : Fin n → MvPolynomial (Fin 4) R) (x : Fin n → Fin 4 → R)
    (q : MvPolynomial (Fin 4) R)
    (hdet : IsUnit (homogeneousFrameEvaluationMatrix frame x).det) (i : Fin n) :
    (homogeneousInterpolationCorrection frame x q).eval (x i) = 0 := by
  have hsum :
      (∑ j, C (homogeneousInterpolationCoefficients frame x q j) * frame j).eval (x i) =
        (Matrix.mulVec (homogeneousFrameEvaluationMatrix frame x)
          (homogeneousInterpolationCoefficients frame x q)) i := by
    simp only [eval_sum, eval_mul, eval_C, Matrix.mulVec, dotProduct,
      homogeneousFrameEvaluationMatrix]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  have heval : Matrix.mulVec (homogeneousFrameEvaluationMatrix frame x)
      (homogeneousInterpolationCoefficients frame x q) = fun j => q.eval (x j) := by
    rw [homogeneousInterpolationCoefficients, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  unfold homogeneousInterpolationCorrection
  rw [eval_sub, hsum, heval]
  exact sub_self _

/-- Coefficient specialization kills the correction coefficients if the
original equation vanishes at the specialized marked points. -/
theorem homogeneousInterpolationCoefficients_map_eq_zero
    {S : Type u} [CommRing S] (f : R →+* S)
    (frame : Fin n → MvPolynomial (Fin 4) R) (x : Fin n → Fin 4 → R)
    (q : MvPolynomial (Fin 4) R)
    (hq : ∀ i, (q.map f).eval (fun j => f (x i j)) = 0) (i : Fin n) :
    f (homogeneousInterpolationCoefficients frame x q i) = 0 := by
  have hzero (j : Fin n) : f (q.eval (x j)) = 0 := by
    rw [MvPolynomial.map_eval]
    exact hq j
  simp [homogeneousInterpolationCoefficients, Matrix.mulVec, dotProduct,
    map_sum, map_mul, hzero]

/-- The corrected equation specializes literally to the original equation;
no compatibility square or inverse-matrix specialization is assumed. -/
theorem homogeneousInterpolationCorrection_map_eq
    {S : Type u} [CommRing S] (f : R →+* S)
    (frame : Fin n → MvPolynomial (Fin 4) R) (x : Fin n → Fin 4 → R)
    (q : MvPolynomial (Fin 4) R)
    (hq : ∀ i, (q.map f).eval (fun j => f (x i j)) = 0) :
    (homogeneousInterpolationCorrection frame x q).map f = q.map f := by
  simp [homogeneousInterpolationCorrection,
    homogeneousInterpolationCoefficients_map_eq_zero f frame x q hq]

end PfaffianDescent
