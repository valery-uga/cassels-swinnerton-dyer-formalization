import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-!
# The actual affine point ideal and its first-order Taylor remainder

This is the ambient algebra needed for the converse to jet vanishing. The
Taylor remainder belongs to the literal square of the evaluation ideal; its
membership is a conclusion, not a supplied first-order completeness premise.

STATUS: UNVERIFIED source draft. Root owns all compiler checks.
-/

namespace PfaffianDescent.Coray

open MvPolynomial

universe u v w

section SquareZero
variable {σ : Type u} [Fintype σ]
variable {R : Type v} {A : Type w} [CommRing R] [CommRing A]

private noncomputable def firstOrderTerm (f : R →+* A) (x y : σ → A)
    (p : MvPolynomial σ R) : A :=
  ∑ i, y i * (pderiv i p).eval₂ f x

private lemma firstOrderTerm_C (f : R →+* A) (x y : σ → A) (a : R) :
    firstOrderTerm f x y (C a) = 0 := by
  simp [firstOrderTerm, pderiv_C]

private lemma firstOrderTerm_add (f : R →+* A) (x y : σ → A)
    (p q : MvPolynomial σ R) :
    firstOrderTerm f x y (p + q) =
      firstOrderTerm f x y p + firstOrderTerm f x y q := by
  simp [firstOrderTerm, mul_add, Finset.sum_add_distrib]

private lemma firstOrderTerm_X (f : R →+* A) (x y : σ → A) (n : σ) :
    firstOrderTerm f x y (X n) = y n := by
  classical
  unfold firstOrderTerm
  rw [Finset.sum_eq_single n]
  · simp
  · intro i _ hi
    simp [pderiv_X_of_ne hi.symm]
  · simp

private lemma firstOrderTerm_mul (f : R →+* A) (x y : σ → A)
    (p q : MvPolynomial σ R) :
    firstOrderTerm f x y (p * q) =
      firstOrderTerm f x y p * q.eval₂ f x +
        p.eval₂ f x * firstOrderTerm f x y q := by
  simp only [firstOrderTerm, pderiv_mul, eval₂_add, eval₂_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

private lemma firstOrderTerm_mem (f : R →+* A) (x y : σ → A)
    (J : Ideal A) (hy : ∀ i, y i ∈ J) (p : MvPolynomial σ R) :
    firstOrderTerm f x y p ∈ J := by
  unfold firstOrderTerm
  exact Submodule.sum_mem J (fun i hi => J.mul_mem_right _ (hy i))

private lemma mul_eq_zero_of_mem_squareZero (J : Ideal A) (hJ : J ^ 2 = ⊥)
    {a b : A} (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
  have h : a * b ∈ J ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  simpa [hJ] using h

private theorem eval₂_add_of_squareZero
    (f : R →+* A) (x y : σ → A)
    (J : Ideal A) (hy : ∀ i, y i ∈ J) (hJ : J ^ 2 = ⊥)
    (p : MvPolynomial σ R) :
    p.eval₂ f (fun i => x i + y i) =
      p.eval₂ f x + ∑ i, y i * (pderiv i p).eval₂ f x := by
  change p.eval₂ f (fun i => x i + y i) =
    p.eval₂ f x + firstOrderTerm f x y p
  induction p using MvPolynomial.induction_on with
  | C a => simp [firstOrderTerm_C]
  | add p q hp hq =>
      simp only [eval₂_add, firstOrderTerm_add, hp, hq]
      ring
  | mul_X p n hp =>
      have hz : firstOrderTerm f x y p * y n = 0 :=
        mul_eq_zero_of_mem_squareZero J hJ
          (firstOrderTerm_mem f x y J hy p) (hy n)
      rw [eval₂_mul, eval₂_X, hp, firstOrderTerm_mul,
        firstOrderTerm_X, eval₂_X]
      simp only [eval₂_mul, eval₂_X, mul_add, add_mul, hz, add_zero]
      ring
end SquareZero

section Point
variable {σ : Type u} [Fintype σ] {M : Type v} [CommRing M]

/-- The actual affine point ideal, the kernel of polynomial evaluation. -/
noncomputable def affinePointIdeal (x : σ → M) : Ideal (MvPolynomial σ M) :=
  RingHom.ker (MvPolynomial.eval x)

/-- Taylor's constant and linear terms account for a polynomial modulo the
literal square of its evaluation ideal. Works in every characteristic. -/
theorem affinePoint_firstOrderRemainder_mem_square
    (x : σ → M) (q : MvPolynomial σ M) :
    q - C (eval x q) -
      ∑ i, C (eval x (pderiv i q)) * (X i - C (x i)) ∈
      affinePointIdeal x ^ 2 := by
  classical
  let m := affinePointIdeal x
  let π := Ideal.Quotient.mk (m ^ 2)
  let f : M →+* (MvPolynomial σ M ⧸ m ^ 2) := π.comp C
  let y : σ → (MvPolynomial σ M ⧸ m ^ 2) := fun i => π (X i) - f (x i)
  have hy : ∀ i, y i ∈ m.cotangentIdeal := by
    intro i
    refine ⟨X i - C (x i), ?_, ?_⟩
    · simp [m, affinePointIdeal, RingHom.mem_ker]
    · simp [y, f, π, map_sub]
  have h := eval₂_add_of_squareZero f (fun i => f (x i)) y
    m.cotangentIdeal hy m.cotangentIdeal_square q
  have hcoords : (fun i => f (x i) + y i) = (fun i => π (X i)) := by
    funext i
    dsimp [y]
    ring
  have heval : q.eval₂ f (fun i => π (X i)) = π q := by
    simpa only [f, MvPolynomial.eval₂_eta] using
      (MvPolynomial.hom_eval₂ q C π X).symm
  rw [hcoords, heval] at h
  have heval_const (r : MvPolynomial σ M) :
      r.eval₂ f (fun i => f (x i)) = f (eval x r) :=
    (MvPolynomial.eval₂_comp f x r).symm
  simp_rw [heval_const] at h
  have hsum : (∑ i, y i * f (eval x (pderiv i q))) =
      ∑ i, f (eval x (pderiv i q)) * y i := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsum] at h
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π (q - C (eval x q) -
    ∑ i, C (eval x (pderiv i q)) * (X i - C (x i))) = 0
  simp only [map_sub, map_sum, map_mul]
  change π q - f (eval x q) -
    ∑ i, f (eval x (pderiv i q)) * y i = 0
  rw [h]
  ring

/-- Vanishing of every ambient first-order coefficient implies actual
membership in the point ideal square. -/
theorem affinePoint_mem_square_of_value_and_partials_zero
    (x : σ → M) (q : MvPolynomial σ M)
    (hvalue : eval x q = 0)
    (hpartials : ∀ i, eval x (pderiv i q) = 0) :
    q ∈ affinePointIdeal x ^ 2 := by
  have h := affinePoint_firstOrderRemainder_mem_square x q
  simpa only [hvalue, hpartials, C_0, zero_mul, Finset.sum_const_zero,
    sub_zero] using h

end Point
end PfaffianDescent.Coray
