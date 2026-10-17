import PfaffianDescent.CyclicCoefficientPointUniversalProperty283

/-! Intake for an actual entire affine closed ideal. The basis consists of
classes of prescribed monomials, with the unit among them. Multiplication
coordinates are constructed, their coefficient point is constructed, and
the resulting polynomial action kernel is proved to equal that same I.
There is no radical, support, reducedness or kernel-agreement premise. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
universe u
variable {A : Type u} [CommRing A] {m n : ℕ}
variable (I : Ideal (MvPolynomial (Fin m) A))
variable (b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I))

def wholeQuotientMultiplicationMatrix283 (i : Fin m) : Matrix (Fin n) (Fin n) A :=
  Algebra.leftMulMatrix b (Ideal.Quotient.mk I (X i))

lemma wholeQuotientMultiplicationMatrix_commute283 (i j : Fin m) :
    wholeQuotientMultiplicationMatrix283 I b i * wholeQuotientMultiplicationMatrix283 I b j =
      wholeQuotientMultiplicationMatrix283 I b j * wholeQuotientMultiplicationMatrix283 I b i := by
  have h := congrArg (Algebra.leftMulMatrix b)
    (mul_comm (Ideal.Quotient.mk I (X i)) (Ideal.Quotient.mk I (X j)))
  simpa only [map_mul, wholeQuotientMultiplicationMatrix283] using h

lemma wholeQuotientMatrixEvaluation_eq283 :
    commutingMatrixEvaluation282 (wholeQuotientMultiplicationMatrix283 I b)
      (wholeQuotientMultiplicationMatrix_commute283 I b) =
    (Algebra.leftMulMatrix b).comp (Ideal.Quotient.mkₐ A I) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [commutingMatrixEvaluation_X282]
  rfl

lemma wholeQuotientPolynomialAction_eq283 (p : MvPolynomial (Fin m) A) :
    commutingMatrixPolynomialAction282 (wholeQuotientMultiplicationMatrix283 I b)
      (wholeQuotientMultiplicationMatrix_commute283 I b) p =
    Matrix.toLinAlgEquiv' (Algebra.leftMulMatrix b (Ideal.Quotient.mk I p)) := by
  change Matrix.toLinAlgEquiv' (commutingMatrixEvaluation282
    (wholeQuotientMultiplicationMatrix283 I b)
    (wholeQuotientMultiplicationMatrix_commute283 I b) p) = _
  rw [wholeQuotientMatrixEvaluation_eq283]
  rfl

lemma wholeQuotientPolynomialAction_ker_eq283 :
    RingHom.ker (commutingMatrixPolynomialAction282 (wholeQuotientMultiplicationMatrix283 I b)
      (wholeQuotientMultiplicationMatrix_commute283 I b)).toRingHom = I := by
  ext p
  change commutingMatrixPolynomialAction282 (wholeQuotientMultiplicationMatrix283 I b)
    (wholeQuotientMultiplicationMatrix_commute283 I b) p = 0 ↔ p ∈ I
  rw [wholeQuotientPolynomialAction_eq283]
  constructor
  · intro hp
    have he : Algebra.leftMulMatrix b (Ideal.Quotient.mk I p) = 0 :=
      Matrix.toLinAlgEquiv'.injective (by simpa only [map_zero] using hp)
    have hq : Ideal.Quotient.mk I p = 0 :=
      (Algebra.leftMulMatrix_injective b) (by simpa only [map_zero] using he)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hq
  · intro hp
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero, map_zero]

variable (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
variable (hb : ∀ j, b j = Ideal.Quotient.mk I (monomial (B j) 1)) (hk : B k = 0)

include hb hk in
lemma wholeQuotientMultiplicationMatrix_cyclic283 (j : Fin n) :
    commutingMatrixPolynomialAction282 (wholeQuotientMultiplicationMatrix283 I b)
      (wholeQuotientMultiplicationMatrix_commute283 I b)
      (monomial (B j) 1) (Pi.single k 1) = Pi.single j 1 := by
  classical
  have hbk : b k = 1 := by
    rw [hb k, hk]
    simp
  rw [commutingMatrixPolynomialAction_apply282, Matrix.mulVec_single_one,
    wholeQuotientMatrixEvaluation_eq283]
  funext a
  change Algebra.leftMulMatrix b (Ideal.Quotient.mk I (monomial (B j) 1)) a k = _
  rw [Algebra.leftMulMatrix_eq_repr_mul, hbk, mul_one, ← hb j, b.repr_self]
  by_cases haj : a = j
  · simp [Finsupp.single_apply, Pi.single_apply, haj]
  · simp [Finsupp.single_apply, Pi.single_apply, haj, Ne.symm haj]

def wholeQuotientCyclicMatrixPoint283 : CyclicCommutingMatrixPoint283 m n B k (A := A) where
  matrices := wholeQuotientMultiplicationMatrix283 I b
  commute := wholeQuotientMultiplicationMatrix_commute283 I b
  cyclic := wholeQuotientMultiplicationMatrix_cyclic283 I b B k hb hk

variable (R : Type u) [CommRing R] [Algebra R A]

def wholeQuotientCyclicCoefficientPoint283 :
    UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A :=
  cyclicCoefficientSpecialization283 R m n B k (wholeQuotientCyclicMatrixPoint283 I b B k hb hk)

lemma wholeQuotientCyclicCoefficientPoint_entry283 (i : Fin m) (a c : Fin n) :
    wholeQuotientCyclicCoefficientPoint283 I b B k hb hk R
      (universalCyclicMultiplicationMatrix282 R m n B k i a c) =
    Algebra.leftMulMatrix b (Ideal.Quotient.mk I (X i)) a c :=
  cyclicCoefficientSpecialization_entry283 R m n B k _ i a c

lemma wholeQuotientCyclicCoefficientPoint_same_whole_ideal283 :
    RingHom.ker (commutingMatrixPolynomialAction282
      (cyclicCoefficientPoint283 R m n B k (wholeQuotientCyclicCoefficientPoint283 I b B k hb hk R)).matrices
      (cyclicCoefficientPoint283 R m n B k (wholeQuotientCyclicCoefficientPoint283 I b B k hb hk R)).commute).toRingHom = I := by
  have hpoint := (cyclicCoefficientPointEquiv283 R m n B k (A := A)).right_inv
    (wholeQuotientCyclicMatrixPoint283 I b B k hb hk)
  change cyclicCoefficientPoint283 R m n B k
    (wholeQuotientCyclicCoefficientPoint283 I b B k hb hk R) =
      wholeQuotientCyclicMatrixPoint283 I b B k hb hk at hpoint
  rw [hpoint]
  exact wholeQuotientPolynomialAction_ker_eq283 I b

end PfaffianDescent
