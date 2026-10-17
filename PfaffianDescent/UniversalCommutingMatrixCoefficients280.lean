import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.FinitePresentation

/-! Source-only280. Actual finitely presented coefficient algebra for
commuting multiplication matrices, with a derived universal tuple and exact
R-algebra-hom universal property. This is a foundational Hilbert-chart cut;
no finite-free ambient quotient or representing Hilbert chart is assumed. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)

abbrev MatrixCoefficientIndex280 := Fin m × (Fin n × Fin n)

abbrev MatrixCoefficientPolynomial280 := MvPolynomial (MatrixCoefficientIndex280 m n) R

def genericMultiplicationMatrix280 (i : Fin m) :
    Matrix (Fin n) (Fin n) (MatrixCoefficientPolynomial280 R m n) :=
  fun a b => X (i, (a, b))

def commutingMatrixRelation280 (q : (Fin m × Fin m) × (Fin n × Fin n)) :
    MatrixCoefficientPolynomial280 R m n :=
  (genericMultiplicationMatrix280 R m n q.1.1 *
      genericMultiplicationMatrix280 R m n q.1.2) q.2.1 q.2.2 -
    (genericMultiplicationMatrix280 R m n q.1.2 *
      genericMultiplicationMatrix280 R m n q.1.1) q.2.1 q.2.2

def commutingMatrixIdeal280 : Ideal (MatrixCoefficientPolynomial280 R m n) :=
  Ideal.span (Set.range (commutingMatrixRelation280 R m n))

abbrev CommutingMatrixCoefficientAlgebra280 :=
  MatrixCoefficientPolynomial280 R m n ⧸ commutingMatrixIdeal280 R m n

def universalMultiplicationMatrix280 (i : Fin m) :
    Matrix (Fin n) (Fin n) (CommutingMatrixCoefficientAlgebra280 R m n) :=
  fun a b => Ideal.Quotient.mk (commutingMatrixIdeal280 R m n) (X (i, (a, b)))

lemma universalMultiplicationMatrix_commute280 (i j : Fin m) :
    universalMultiplicationMatrix280 R m n i * universalMultiplicationMatrix280 R m n j =
      universalMultiplicationMatrix280 R m n j * universalMultiplicationMatrix280 R m n i := by
  classical
  apply Matrix.ext
  intro a b
  apply sub_eq_zero.mp
  have hmem : commutingMatrixRelation280 R m n ((i, j), (a, b)) ∈
      commutingMatrixIdeal280 R m n :=
    Ideal.subset_span ⟨((i, j), (a, b)), rfl⟩
  have hz : Ideal.Quotient.mk (commutingMatrixIdeal280 R m n)
      (commutingMatrixRelation280 R m n ((i, j), (a, b))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  simpa [commutingMatrixRelation280, genericMultiplicationMatrix280,
    universalMultiplicationMatrix280, Matrix.mul_apply, map_sum] using hz

lemma commutingMatrixIdeal_fg280 : (commutingMatrixIdeal280 R m n).FG := by
  change (Submodule.span (MatrixCoefficientPolynomial280 R m n)
    (Set.range (commutingMatrixRelation280 R m n))).FG
  exact Submodule.fg_span (Set.finite_range _)

lemma commutingMatrixCoefficientAlgebra_finitePresentation280 :
    Algebra.FinitePresentation R (CommutingMatrixCoefficientAlgebra280 R m n) :=
  Algebra.FinitePresentation.quotient (R := R) (commutingMatrixIdeal_fg280 R m n)

variable {A : Type u} [CommRing A] [Algebra R A]

def multiplicationMatrixEntries280 (M : Fin m → Matrix (Fin n) (Fin n) A) :
    MatrixCoefficientIndex280 m n → A := fun q => M q.1 q.2.1 q.2.2

lemma commutingMatrixRelation_aeval280
    (M : Fin m → Matrix (Fin n) (Fin n) A)
    (q : (Fin m × Fin m) × (Fin n × Fin n)) :
    aeval (R := R) (multiplicationMatrixEntries280 m n M)
      (commutingMatrixRelation280 R m n q) =
    (M q.1.1 * M q.1.2) q.2.1 q.2.2 -
      (M q.1.2 * M q.1.1) q.2.1 q.2.2 := by
  classical
  simp [commutingMatrixRelation280, genericMultiplicationMatrix280,
    multiplicationMatrixEntries280, Matrix.mul_apply, map_sum]

lemma commutingMatrixIdeal_le_ker_aeval280
    (M : Fin m → Matrix (Fin n) (Fin n) A)
    (hM : ∀ i j, M i * M j = M j * M i) :
    commutingMatrixIdeal280 R m n ≤
      RingHom.ker (aeval (R := R) (multiplicationMatrixEntries280 m n M)).toRingHom := by
  change Ideal.span (Set.range (commutingMatrixRelation280 R m n)) ≤ _
  apply Ideal.span_le.mpr
  rintro x ⟨q, rfl⟩
  change aeval (R := R) (multiplicationMatrixEntries280 m n M)
    (commutingMatrixRelation280 R m n q) = 0
  rw [commutingMatrixRelation_aeval280, hM q.1.1 q.1.2, sub_self]

def commutingMatrixSpecialization280
    (M : Fin m → Matrix (Fin n) (Fin n) A)
    (hM : ∀ i j, M i * M j = M j * M i) :
    CommutingMatrixCoefficientAlgebra280 R m n →ₐ[R] A :=
  Ideal.Quotient.liftₐ (commutingMatrixIdeal280 R m n)
    (aeval (R := R) (multiplicationMatrixEntries280 m n M))
    (fun x hx => RingHom.mem_ker.mp
      (commutingMatrixIdeal_le_ker_aeval280 R m n M hM hx))

lemma commutingMatrixSpecialization_entry280
    (M : Fin m → Matrix (Fin n) (Fin n) A)
    (hM : ∀ i j, M i * M j = M j * M i) (i : Fin m) (a b : Fin n) :
    commutingMatrixSpecialization280 R m n M hM
      (universalMultiplicationMatrix280 R m n i a b) = M i a b := by
  change (Ideal.Quotient.lift (commutingMatrixIdeal280 R m n)
    (aeval (R := R) (multiplicationMatrixEntries280 m n M)).toRingHom
    (fun x hx => RingHom.mem_ker.mp
      (commutingMatrixIdeal_le_ker_aeval280 R m n M hM hx)))
    (Ideal.Quotient.mk (commutingMatrixIdeal280 R m n) (X (i, (a, b)))) = M i a b
  exact (Ideal.Quotient.lift_mk _ _ _).trans
    (MvPolynomial.aeval_X (multiplicationMatrixEntries280 m n M) (i, (a, b)))

lemma commutingMatrixCoefficient_hom_ext280
    {f g : CommutingMatrixCoefficientAlgebra280 R m n →ₐ[R] A}
    (h : ∀ i a b, f (universalMultiplicationMatrix280 R m n i a b) =
      g (universalMultiplicationMatrix280 R m n i a b)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨i, a, b⟩
  exact h i a b

def coefficientPointMultiplicationMatrix280
    (f : CommutingMatrixCoefficientAlgebra280 R m n →ₐ[R] A) (i : Fin m) :
    Matrix (Fin n) (Fin n) A :=
  fun a b => f (universalMultiplicationMatrix280 R m n i a b)

lemma coefficientPointMultiplicationMatrix_commute280
    (f : CommutingMatrixCoefficientAlgebra280 R m n →ₐ[R] A) (i j : Fin m) :
    coefficientPointMultiplicationMatrix280 R m n f i *
      coefficientPointMultiplicationMatrix280 R m n f j =
    coefficientPointMultiplicationMatrix280 R m n f j *
      coefficientPointMultiplicationMatrix280 R m n f i := by
  classical
  apply Matrix.ext
  intro a b
  have h := congrArg f (congrFun
    (congrFun (universalMultiplicationMatrix_commute280 R m n i j) a) b)
  simpa [coefficientPointMultiplicationMatrix280, Matrix.mul_apply, map_sum] using h

def commutingMatrixCoefficientPointEquiv280 :
    (CommutingMatrixCoefficientAlgebra280 R m n →ₐ[R] A) ≃
      {M : Fin m → Matrix (Fin n) (Fin n) A // ∀ i j, M i * M j = M j * M i} where
  toFun f := ⟨coefficientPointMultiplicationMatrix280 R m n f,
    coefficientPointMultiplicationMatrix_commute280 R m n f⟩
  invFun M := commutingMatrixSpecialization280 R m n M.val M.property
  left_inv f := by
    apply commutingMatrixCoefficient_hom_ext280 R m n
    intro i a b
    exact commutingMatrixSpecialization_entry280 R m n _ _ i a b
  right_inv M := by
    apply Subtype.ext
    funext i a b
    exact commutingMatrixSpecialization_entry280 R m n _ _ i a b

lemma coefficientPointMultiplicationMatrix_comp280
    {B : Type u} [CommRing B] [Algebra R B]
    (f : CommutingMatrixCoefficientAlgebra280 R m n →ₐ[R] A) (h : A →ₐ[R] B)
    (i : Fin m) (a b : Fin n) :
    coefficientPointMultiplicationMatrix280 R m n (h.comp f) i a b =
      h (coefficientPointMultiplicationMatrix280 R m n f i a b) := rfl

end PfaffianDescent
