import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Ideal.Operations

/-!
# First-order Taylor expansion in a square-zero ideal

This identity isolates the algebraic step needed to turn a section of the
first-order thickening of an affine cubic chart into a Jacobian relation.
It works over an arbitrary commutative ground ring, including in positive
characteristic.
-/

namespace PfaffianDescent

open MvPolynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]

private noncomputable def firstOrderTerm (f : R →+* A) (x y : Fin 4 → A)
    (p : MvPolynomial (Fin 4) R) : A :=
  ∑ i : Fin 4, y i * (pderiv i p).eval₂ f x

private lemma firstOrderTerm_C (f : R →+* A) (x y : Fin 4 → A) (a : R) :
    firstOrderTerm f x y (C a) = 0 := by
  simp [firstOrderTerm]

private lemma firstOrderTerm_add (f : R →+* A) (x y : Fin 4 → A)
    (p q : MvPolynomial (Fin 4) R) :
    firstOrderTerm f x y (p + q) =
      firstOrderTerm f x y p + firstOrderTerm f x y q := by
  simp [firstOrderTerm, mul_add, Finset.sum_add_distrib]

private lemma firstOrderTerm_X (f : R →+* A) (x y : Fin 4 → A) (n : Fin 4) :
    firstOrderTerm f x y (X n) = y n := by
  classical
  unfold firstOrderTerm
  rw [Finset.sum_eq_single n]
  · simp
  · intro i _ hi
    simp [pderiv_X_of_ne hi.symm]
  · simp

private lemma firstOrderTerm_mul (f : R →+* A) (x y : Fin 4 → A)
    (p q : MvPolynomial (Fin 4) R) :
    firstOrderTerm f x y (p * q) =
      firstOrderTerm f x y p * q.eval₂ f x +
        p.eval₂ f x * firstOrderTerm f x y q := by
  simp only [firstOrderTerm, pderiv_mul, eval₂_add, eval₂_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

private lemma firstOrderTerm_mem (f : R →+* A) (x y : Fin 4 → A)
    (J : Ideal A) (hy : ∀ i, y i ∈ J) (p : MvPolynomial (Fin 4) R) :
    firstOrderTerm f x y p ∈ J := by
  unfold firstOrderTerm
  exact Submodule.sum_mem J (fun i hi => J.mul_mem_right _ (hy i))

private lemma mul_eq_zero_of_mem_squareZero (J : Ideal A) (hJ : J ^ 2 = ⊥)
    {a b : A} (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
  have h : a * b ∈ J ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul ha hb
  simpa [hJ] using h

/-- Exact first-order Taylor expansion when the coordinate increments lie
in a square-zero ideal. No factorials or characteristic assumptions enter. -/
theorem mvPolynomial_eval₂_add_of_squareZero
    (f : R →+* A) (x y : Fin 4 → A)
    (J : Ideal A) (hy : ∀ i, y i ∈ J) (hJ : J ^ 2 = ⊥)
    (p : MvPolynomial (Fin 4) R) :
    p.eval₂ f (fun i => x i + y i) =
      p.eval₂ f x + ∑ i : Fin 4, y i * (pderiv i p).eval₂ f x := by
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

end PfaffianDescent
