import PfaffianDescent.Basic
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace PfaffianDescent
open Polynomial Module
open scoped BigOperators
attribute [local instance] Polynomial.algebra

section
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {m : ℕ}

/-- Apply each ground-field basis coordinate to the coefficients of a polynomial. -/
noncomputable def basisPolynomialCoordinates (b : Basis (Fin m) K L) (p : L[X]) : Vec K[X] m :=
  fun i => ∑ n ∈ p.support, monomial n (b.repr (p.coeff n) i)

theorem basisPolynomialCoordinates_coeff (b : Basis (Fin m) K L) (p : L[X]) (i : Fin m) (n : ℕ) :
    (basisPolynomialCoordinates b p i).coeff n = b.repr (p.coeff n) i := by
  classical
  by_cases hn : n ∈ p.support
  · simp [basisPolynomialCoordinates, finsetSum_coeff, coeff_monomial, hn]
  · simp [basisPolynomialCoordinates, finsetSum_coeff, coeff_monomial, hn, notMem_support_iff.mp hn]

/-- Reconstruct extension-coefficient polynomials from their ground-field coordinate polynomials. -/
noncomputable def basisPolynomialLift (b : Basis (Fin m) K L) : Vec K[X] m →ₗ[K[X]] L[X] :=
  Fintype.linearCombination K[X] (fun i => C (b i))

theorem basisPolynomialLift_reconstruct (b : Basis (Fin m) K L) (p : L[X]) :
    basisPolynomialLift b (basisPolynomialCoordinates b p) = p := by
  ext n
  simp only [basisPolynomialLift, Fintype.linearCombination_apply, Algebra.smul_def,
    Polynomial.algebraMap_def, Polynomial.coe_mapRingHom, finsetSum_coeff, coeff_mul_C,
    coeff_map, basisPolynomialCoordinates_coeff]
  simpa only [Algebra.smul_def] using b.sum_repr (p.coeff n)

theorem basisPolynomialCoordinates_eval_zero (b : Basis (Fin m) K L) (p : L[X]) (i : Fin m) :
    (basisPolynomialCoordinates b p i).eval 0 = b.repr (p.eval 0) i := by
  rw [← coeff_zero_eq_eval_zero, basisPolynomialCoordinates_coeff, coeff_zero_eq_eval_zero]

end

section
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {m n : ℕ}

theorem linearMap_mulVec (f : Vec R m →ₗ[R] V) (A : Matrix (Fin m) (Fin n) R) (x : Vec R n) :
    f (A.mulVec x) = ∑ j, x j • f (fun i => A i j) := by
  have h : A.mulVec x = ∑ j, x j • (fun i => A i j) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [h, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact map_smul f _ _

end
end PfaffianDescent
