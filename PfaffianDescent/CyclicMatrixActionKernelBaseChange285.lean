import PfaffianDescent.CyclicActionKernelFiniteGenerators285
import PfaffianDescent.CommutingMatrixPolynomialAction282
import Mathlib.RingTheory.Ideal.Maps

noncomputable section
namespace PfaffianDescent
open MvPolynomial
open scoped BigOperators Matrix
universe u v
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] {m n : ℕ}

lemma commutingMatrixAction_border_coefficients285
    (M : Fin m → Matrix (Fin n) (Fin n) R)
    (hM : ∀ i j, M i * M j = M j * M i)
    (B : Fin n → (Fin m →₀ ℕ)) (i : Fin m) (j : Fin n) :
    cyclicActionBorderRelation285 (commutingMatrixPolynomialAction282 M hM) B (i, j) =
      X i * monomial (B j) 1 - ∑ a : Fin n, C (M i a j) * monomial (B a) 1 := by
  change X i * monomial (B j) 1 -
    (∑ a : Fin n, (commutingMatrixPolynomialAction282 M hM (X i)
      (Pi.single j 1)) a • monomial (B a) 1) = _
  simp only [commutingMatrixPolynomialAction_X282,
    Matrix.toLinAlgEquiv'_apply, Matrix.mulVec_single_one, Matrix.col_apply,
    MvPolynomial.smul_eq_C_mul]

lemma cyclicMonomialLift_map285 (f : R →+* S)
    (B : Fin n → (Fin m →₀ ℕ)) (x : Fin n → R) :
    MvPolynomial.map f (cyclicMonomialLift285 B x) =
      cyclicMonomialLift285 B (fun j => f (x j)) := by
  classical
  change MvPolynomial.map f (∑ j : Fin n, x j • monomial (B j) 1) =
    ∑ j : Fin n, f (x j) • monomial (B j) 1
  simp only [MvPolynomial.smul_eq_C_mul,
    map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_monomial, map_one]

lemma cyclicActionUnitRelation_map285 (f : R →+* S)
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) :
    MvPolynomial.map f (cyclicActionUnitRelation285 (R := R) B k) =
      cyclicActionUnitRelation285 (R := S) B k := by
  simp only [cyclicActionUnitRelation285, map_sub, MvPolynomial.map_monomial, map_one]

lemma cyclicActionBorderRelation_map285 (f : R →+* S)
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (tau : MvPolynomial (Fin m) S →ₐ[S] Module.End S (Fin n → S))
    (hX : ∀ i j a, (tau (X i) (Pi.single j 1)) a =
      f ((rho (X i) (Pi.single j 1)) a))
    (B : Fin n → (Fin m →₀ ℕ)) (q : Fin m × Fin n) :
    MvPolynomial.map f (cyclicActionBorderRelation285 rho B q) =
      cyclicActionBorderRelation285 tau B q := by
  rw [cyclicActionBorderRelation285, map_sub, map_mul, MvPolynomial.map_X,
    MvPolynomial.map_monomial, map_one, cyclicMonomialLift_map285,
    cyclicActionBorderRelation285]
  congr 1
  congr 1
  funext a
  exact (hX q.1 q.2 a).symm

lemma cyclicActionGeneratorIdeal_map285 (f : R →+* S)
    (rho : MvPolynomial (Fin m) R →ₐ[R] Module.End R (Fin n → R))
    (tau : MvPolynomial (Fin m) S →ₐ[S] Module.End S (Fin n → S))
    (hX : ∀ i j a, (tau (X i) (Pi.single j 1)) a =
      f ((rho (X i) (Pi.single j 1)) a))
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) :
    (cyclicActionGeneratorIdeal285 rho B k).map (MvPolynomial.map f) =
      cyclicActionGeneratorIdeal285 tau B k := by
  rw [cyclicActionGeneratorIdeal285, Ideal.map_span, cyclicActionGeneratorIdeal285]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with rfl | ⟨ij, rfl⟩
    · rw [cyclicActionUnitRelation_map285]
      exact Set.mem_insert _ _
    · rw [cyclicActionBorderRelation_map285 f rho tau hX]
      exact Set.mem_insert_of_mem _ (Set.mem_range_self ij)
  · rintro (rfl | ⟨ij, rfl⟩)
    · exact ⟨cyclicActionUnitRelation285 (R := R) B k, Set.mem_insert _ _,
        cyclicActionUnitRelation_map285 f B k⟩
    · exact ⟨cyclicActionBorderRelation285 rho B ij,
        Set.mem_insert_of_mem _ (Set.mem_range_self ij),
        cyclicActionBorderRelation_map285 f rho tau hX B ij⟩

/-- Coefficient naturality with independent coefficient-ring universes. -/
lemma commutingMatrixEvaluation_map_independent285
    (M : Fin m → Matrix (Fin n) (Fin n) R)
    (hM : ∀ i j, M i * M j = M j * M i) (f : R →+* S)
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

lemma commutingMatrixAction_cyclic_map285
    (M : Fin m → Matrix (Fin n) (Fin n) R)
    (hM : ∀ i j, M i * M j = M j * M i) (f : R →+* S)
    (N : Fin m → Matrix (Fin n) (Fin n) S)
    (hN : ∀ i j, N i * N j = N j * N i)
    (hMN : ∀ i, N i = (M i).map f)
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (hB : ∀ j, commutingMatrixPolynomialAction282 M hM (monomial (B j) 1)
      (Pi.single k 1) = Pi.single j 1) :
    ∀ j, commutingMatrixPolynomialAction282 N hN (monomial (B j) 1)
      (Pi.single k 1) = Pi.single j 1 := by
  classical
  intro j
  have hnat := commutingMatrixEvaluation_map_independent285 M hM f N hN hMN
    (monomial (B j) 1)
  simp only [MvPolynomial.map_monomial, map_one] at hnat
  rw [commutingMatrixPolynomialAction_apply282, Matrix.mulVec_single_one, hnat]
  funext a
  change f (commutingMatrixEvaluation282 M hM (monomial (B j) 1) a k) =
    (Pi.single j 1 : Fin n → S) a
  have hj := congrFun (hB j) a
  simp only [commutingMatrixPolynomialAction_apply282, Matrix.mulVec_single_one,
    Matrix.col_apply] at hj
  rw [hj]
  by_cases haj : a = j
  · simp [Pi.single_apply, apply_ite, haj]
  · simp [Pi.single_apply, apply_ite, haj]

/-- Arbitrary coefficient change commutes with the whole action ideal here
because the explicitly derived finite generators commute with that change. -/
lemma commutingMatrixActionKernel_baseChange285
    (M : Fin m → Matrix (Fin n) (Fin n) R)
    (hM : ∀ i j, M i * M j = M j * M i) (f : R →+* S)
    (N : Fin m → Matrix (Fin n) (Fin n) S)
    (hN : ∀ i j, N i * N j = N j * N i)
    (hMN : ∀ i, N i = (M i).map f)
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (hB : ∀ j, commutingMatrixPolynomialAction282 M hM (monomial (B j) 1)
      (Pi.single k 1) = Pi.single j 1) :
    (RingHom.ker (commutingMatrixPolynomialAction282 M hM).toRingHom).map
      (MvPolynomial.map f) = RingHom.ker (commutingMatrixPolynomialAction282 N hN).toRingHom := by
  have hBN := commutingMatrixAction_cyclic_map285 M hM f N hN hMN B k hB
  rw [cyclicActionKernel_eq_generatorIdeal285 _ B k hB,
    cyclicActionKernel_eq_generatorIdeal285 _ B k hBN]
  apply cyclicActionGeneratorIdeal_map285
  intro i j a
  simp only [commutingMatrixPolynomialAction_X282, Matrix.toLinAlgEquiv'_apply,
    Matrix.mulVec_single_one, Matrix.col_apply, hMN, Matrix.map_apply]

lemma commutingMatrix_tuple_map_commute285
    (M : Fin m → Matrix (Fin n) (Fin n) R)
    (hM : ∀ i j, M i * M j = M j * M i) (f : R →+* S) (i j : Fin m) :
    (M i).map f * (M j).map f = (M j).map f * (M i).map f := by
  have h := congrArg f.mapMatrix (hM i j)
  simpa only [RingHom.mapMatrix_apply, Matrix.map_mul] using h

lemma commutingMatrixActionKernel_mapped285
    (M : Fin m → Matrix (Fin n) (Fin n) R)
    (hM : ∀ i j, M i * M j = M j * M i) (f : R →+* S)
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (hB : ∀ j, commutingMatrixPolynomialAction282 M hM (monomial (B j) 1)
      (Pi.single k 1) = Pi.single j 1) :
    (RingHom.ker (commutingMatrixPolynomialAction282 M hM).toRingHom).map
      (MvPolynomial.map f) =
      RingHom.ker (commutingMatrixPolynomialAction282 (fun i => (M i).map f)
        (commutingMatrix_tuple_map_commute285 M hM f)).toRingHom :=
  commutingMatrixActionKernel_baseChange285 M hM f (fun i => (M i).map f)
    (commutingMatrix_tuple_map_commute285 M hM f) (fun _ => rfl) B k hB

end PfaffianDescent
