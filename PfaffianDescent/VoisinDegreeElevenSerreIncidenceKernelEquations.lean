import PfaffianDescent.VoisinDegreeElevenSerreIncidenceKernelProjectiveEmbedding
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Actual coordinate-ring identification for a split evaluation kernel

A literal split decomposition of the nine coordinates identifies the quotient
by the six evaluation equations with the three-variable polynomial ring. No
field dimension or scheme dimension certificate is used.
-/
noncomputable section
open MvPolynomial
namespace PfaffianDescent
universe u
variable {R : Type u} [CommRing R]

lemma serreRectangularLinearCoordinate_add {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) R) (i : Fin m) :
    rectangularLinearCoordinate (A + B) i =
      rectangularLinearCoordinate A i + rectangularLinearCoordinate B i := by
  simp [rectangularLinearCoordinate, Matrix.mulVec, dotProduct,
    add_mul, Finset.sum_add_distrib]

lemma serreRectangularLinearCoordinate_mul {l m n : ℕ}
    (T : Matrix (Fin l) (Fin m) R) (A : Matrix (Fin m) (Fin n) R) (i : Fin l) :
    rectangularLinearCoordinate (T * A) i =
      ∑ j, MvPolynomial.C (T i j) * rectangularLinearCoordinate A j := by
  unfold rectangularLinearCoordinate
  rw [Matrix.map_mul, ← Matrix.mulVec_mulVec]
  rfl

def serreEvaluationEquationIdeal (A : Matrix (Fin 6) (Fin 9) R) :
    Ideal (MvPolynomial (Fin 9) R) :=
  Ideal.span (Set.range (rectangularLinearCoordinate A))

lemma serreEvaluationEquationIdeal_le_ker
    (A : Matrix (Fin 6) (Fin 9) R) (M : Matrix (Fin 9) (Fin 3) R)
    (hAM : A * M = 0) :
    serreEvaluationEquationIdeal A ≤ RingHom.ker (rectangularSubstitution M).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact serreKernelFrameProjectiveEmbedding_evaluationEquations A M hAM i

lemma serreEvaluationEquationIdeal_quotientCoordinate
    (A : Matrix (Fin 6) (Fin 9) R) (M : Matrix (Fin 9) (Fin 3) R)
    (N : Matrix (Fin 3) (Fin 9) R) (D : Matrix (Fin 9) (Fin 6) R)
    (hsplit : M * N + D * A = 1) (i : Fin 9) :
    Ideal.Quotient.mk (serreEvaluationEquationIdeal A)
      (rectangularLinearCoordinate (M * N) i) =
    Ideal.Quotient.mk (serreEvaluationEquationIdeal A) (X i) := by
  let q := Ideal.Quotient.mk (serreEvaluationEquationIdeal A)
  have hzero : ∀ j : Fin 6, q (rectangularLinearCoordinate A j) = 0 := by
    intro j
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  have hDA : q (rectangularLinearCoordinate (D * A) i) = 0 := by
    rw [serreRectangularLinearCoordinate_mul, map_sum]
    simp only [map_mul, hzero, mul_zero, Finset.sum_const_zero]
  have h := congrArg (fun E => q (rectangularLinearCoordinate E i)) hsplit
  rw [serreRectangularLinearCoordinate_add, map_add, hDA, add_zero] at h
  have hone : rectangularLinearCoordinate (1 : Matrix (Fin 9) (Fin 9) R) i = X i := by
    unfold rectangularLinearCoordinate
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  rw [hone] at h
  exact h

/-- The literal quotient by evaluation equations is the three-coordinate
kernel ring whenever the split matrices satisfy their actual identities. -/
def serreEvaluationEquationQuotientEquiv
    (A : Matrix (Fin 6) (Fin 9) R) (M : Matrix (Fin 9) (Fin 3) R)
    (N : Matrix (Fin 3) (Fin 9) R) (D : Matrix (Fin 9) (Fin 6) R)
    (hAM : A * M = 0) (hNM : N * M = 1) (hsplit : M * N + D * A = 1) :
    (MvPolynomial (Fin 9) R ⧸ serreEvaluationEquationIdeal A) ≃ₐ[R]
      MvPolynomial (Fin 3) R := by
  let f := Ideal.Quotient.liftₐ (serreEvaluationEquationIdeal A)
    (rectangularSubstitution M) (fun a ha => serreEvaluationEquationIdeal_le_ker A M hAM ha)
  let g := (Ideal.Quotient.mkₐ R (serreEvaluationEquationIdeal A)).comp
    (rectangularSubstitution N)
  apply AlgEquiv.ofAlgHom f g
  · apply MvPolynomial.algHom_ext
    intro i
    change rectangularSubstitution M (rectangularSubstitution N (X i)) = X i
    rw [← AlgHom.comp_apply, rectangularSubstitution_comp, hNM,
      rectangularSubstitution_one]
    rfl
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    change Ideal.Quotient.mk (serreEvaluationEquationIdeal A)
      (rectangularSubstitution N (rectangularSubstitution M (X i))) =
      Ideal.Quotient.mk (serreEvaluationEquationIdeal A) (X i)
    rw [← AlgHom.comp_apply, rectangularSubstitution_comp, rectangularSubstitution_X]
    exact serreEvaluationEquationIdeal_quotientCoordinate A M N D hsplit i

end PfaffianDescent
