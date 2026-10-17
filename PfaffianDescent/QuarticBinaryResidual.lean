import PfaffianDescent.QuarticBinaryForms
import PfaffianDescent.QuarticResidualDoublePoint

/-!
# Projective residual points for binary degree-nine forms

This packages the univariate residual-root argument in homogeneous binary
coordinates, including the residual point at infinity.
-/

namespace PfaffianDescent
namespace QuarticNet

open MvPolynomial

universe u

variable {k : Type u} [Field k]

noncomputable def binaryDehomogenize :
    MvPolynomial (Fin 2) k →ₐ[k] Polynomial k :=
  aeval ![1, Polynomial.X]

theorem binaryDehomogenize_binaryForm (n : ℕ) (q : Fin (n + 1) → k) :
    binaryDehomogenize (binaryForm n q) =
      ∑ i, Polynomial.C (q i) * Polynomial.X ^ i.val := by
  simp [binaryDehomogenize, binaryForm, binaryExponent, aeval_monomial,
    Finsupp.prod_add_index, Finsupp.prod_single_index]

theorem binaryDehomogenize_binaryForm_coeff (n : ℕ) (q : Fin (n + 1) → k)
    (i : Fin (n + 1)) :
    (binaryDehomogenize (binaryForm n q)).coeff i.val = q i := by
  classical
  rw [binaryDehomogenize_binaryForm]
  simp [Polynomial.coeff_sum, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Fin.val_inj]

theorem binaryForm_atInfinity (n : ℕ) (q : Fin (n + 1) → k) :
    aeval ![0, 1] (binaryForm n q) = q (Fin.last n) := by
  classical
  simp only [binaryForm, map_sum]
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp [binaryExponent, aeval_monomial, Finsupp.prod_add_index,
      Finsupp.prod_single_index]
  · intro i _ hi
    have hni : n - i.val ≠ 0 := by
      intro h
      apply hi
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    simp [binaryExponent, aeval_monomial, Finsupp.prod_add_index,
      Finsupp.prod_single_index, hni]
  · simp

theorem binaryDehomogenize_natDegree (n : ℕ) (F : MvPolynomial (Fin 2) k)
    (hF : F.IsHomogeneous n) : (binaryDehomogenize F).natDegree ≤ n := by
  rw [← binaryForm_exhaustive n F hF, binaryDehomogenize_binaryForm]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans
    (Nat.le_of_lt_succ i.isLt)

theorem binaryDehomogenize_topCoeff (n : ℕ) (F : MvPolynomial (Fin 2) k)
    (hF : F.IsHomogeneous n) :
    (binaryDehomogenize F).coeff n = aeval ![0, 1] F := by
  rw [← binaryForm_exhaustive n F hF, binaryForm_atInfinity]
  exact binaryDehomogenize_binaryForm_coeff n _ (Fin.last n)

theorem binaryDehomogenize_eval {A : Type u} [CommRing A] [Algebra k A]
    (x : A) (F : MvPolynomial (Fin 2) k) :
    Polynomial.aeval x (binaryDehomogenize F) = aeval ![1, x] F := by
  have h : (Polynomial.aeval x).comp (binaryDehomogenize (k := k)) = aeval ![1, x] := by
    ext i : 1
    fin_cases i <;> simp [binaryDehomogenize]
  exact AlgHom.congr_fun h F

/-- The projective residual point, including the case where it lies at
infinity. -/
theorem binary_degree_nine_residual_point {L : Type u} [Field L] [Algebra k L]
    [Algebra.IsSeparable k L] (a b : L) (hb : b ≠ 0)
    (ha : (minpoly k a).natDegree = 4)
    (F : MvPolynomial (Fin 2) k) (hF : F.IsHomogeneous 9)
    (hjet : aeval ![1, TrivSqZeroExt.inl a + TrivSqZeroExt.inr b] F =
      (0 : DualNumber L)) :
    ∃ x : Fin 2 → k, x ≠ 0 ∧ aeval x F = 0 := by
  by_cases hinf : aeval ![0, 1] F = (0 : k)
  · refine ⟨![0, 1], ?_, hinf⟩
    intro h
    exact (one_ne_zero : (1 : k) ≠ 0) (by simpa using congrFun h (1 : Fin 2))
  have hdeg : (binaryDehomogenize F).natDegree = 9 := by
    apply le_antisymm (binaryDehomogenize_natDegree 9 F hF)
    apply Polynomial.le_natDegree_of_ne_zero
    rwa [binaryDehomogenize_topCoeff 9 F hF]
  obtain ⟨r, hr⟩ := degree_nine_root_of_quartic_double_point a b hb ha
    (binaryDehomogenize F) hdeg (by rwa [binaryDehomogenize_eval])
  refine ⟨![1, r], ?_, ?_⟩
  · intro h
    exact (one_ne_zero : (1 : k) ≠ 0) (by simpa using congrFun h (0 : Fin 2))
  · rw [← binaryDehomogenize_eval]
    simpa [Polynomial.IsRoot] using hr

end QuarticNet
end PfaffianDescent
