import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A polynomial action constructed from the given commuting matrices.
The action is not a caller premise. Coefficient-map compatibility is an
actual equality of the resulting matrix evaluations. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial
open scoped IsMulCommutative Matrix
universe u
variable {R : Type u} [CommRing R] {m n : ℕ}
variable (M : Fin m → Matrix (Fin n) (Fin n) R)
variable (hM : ∀ i j, M i * M j = M j * M i)

def commutingMatrixEvaluation282 :
    MvPolynomial (Fin m) R →ₐ[R] Matrix (Fin n) (Fin n) R := by
  let T := Algebra.adjoin R (Set.range M)
  letI : IsMulCommutative T := Algebra.isMulCommutative_adjoin R (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hM i j)
  let generators : Fin m → T := fun i =>
    ⟨M i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  exact T.val.comp (MvPolynomial.aeval generators)

lemma commutingMatrixEvaluation_X282 (i : Fin m) :
    commutingMatrixEvaluation282 M hM (X i) = M i := by
  simp [commutingMatrixEvaluation282]

lemma commutingMatrixEvaluation_C282 (r : R) :
    commutingMatrixEvaluation282 M hM (C r) =
      algebraMap R (Matrix (Fin n) (Fin n) R) r := by
  exact (commutingMatrixEvaluation282 M hM).commutes r

lemma commutingMatrixEvaluation_map282
    {S : Type u} [CommRing S] (f : R →+* S)
    (N : Fin m → Matrix (Fin n) (Fin n) S)
    (hN : ∀ i j, N i * N j = N j * N i)
    (hMN : ∀ i, N i = (M i).map f) (p : MvPolynomial (Fin m) R) :
    commutingMatrixEvaluation282 N hN (MvPolynomial.map f p) =
      (commutingMatrixEvaluation282 M hM p).map f := by
  have he : (commutingMatrixEvaluation282 N hN).toRingHom.comp (MvPolynomial.map f) =
      f.mapMatrix.comp (commutingMatrixEvaluation282 M hM).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change commutingMatrixEvaluation282 N hN (MvPolynomial.map f (C r)) =
        (commutingMatrixEvaluation282 M hM (C r)).map f
      rw [MvPolynomial.map_C, commutingMatrixEvaluation_C282, commutingMatrixEvaluation_C282]
      apply Matrix.ext
      intro a b
      by_cases hab : a = b
      · simp [Matrix.algebraMap_matrix_apply, Matrix.map_apply, hab]
      · simp [Matrix.algebraMap_matrix_apply, Matrix.map_apply, hab]
    · intro i
      change commutingMatrixEvaluation282 N hN (MvPolynomial.map f (X i)) =
        (commutingMatrixEvaluation282 M hM (X i)).map f
      rw [MvPolynomial.map_X, commutingMatrixEvaluation_X282, commutingMatrixEvaluation_X282]
      exact hMN i
  exact congrArg (fun g : MvPolynomial (Fin m) R →+* Matrix (Fin n) (Fin n) S => g p) he

def commutingMatrixPolynomialAction282 :
    MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R) :=
  Matrix.toLinAlgEquiv'.toAlgHom.comp (commutingMatrixEvaluation282 M hM)

lemma commutingMatrixPolynomialAction_apply282 (p : MvPolynomial (Fin m) R)
    (v : Fin n → R) :
    commutingMatrixPolynomialAction282 M hM p v =
      commutingMatrixEvaluation282 M hM p *ᵥ v := rfl

lemma commutingMatrixPolynomialAction_X282 (i : Fin m) :
    commutingMatrixPolynomialAction282 M hM (X i) = Matrix.toLinAlgEquiv' (M i) := by
  change Matrix.toLinAlgEquiv' (commutingMatrixEvaluation282 M hM (X i)) = _
  rw [commutingMatrixEvaluation_X282]

end PfaffianDescent
