import PfaffianDescent.UniversalCyclicMatrixQuotient282

/-! Primitive matrix/monomial equations represent points of the actual
cyclic coefficient algebra. This is an algebra-hom universal property,
not an assumed scheme representation. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
variable {A : Type u} [CommRing A] [Algebra R A]

structure CyclicCommutingMatrixPoint283 where
  matrices : Fin m → Matrix (Fin n) (Fin n) A
  commute : ∀ i j, matrices i * matrices j = matrices j * matrices i
  cyclic : ∀ j, commutingMatrixPolynomialAction282 matrices commute
    (monomial (B j) 1) (Pi.single k 1) = Pi.single j 1

lemma CyclicCommutingMatrixPoint283.ext
    {x y : CyclicCommutingMatrixPoint283 m n B k (A := A)}
    (h : x.matrices = y.matrices) : x = y := by
  cases x
  cases y
  cases h
  rfl

lemma universalCyclicRelation_specialization283
    (M : Fin m → Matrix (Fin n) (Fin n) A)
    (hM : ∀ i j, M i * M j = M j * M i) (j a : Fin n) :
    commutingMatrixSpecialization280 R m n M hM
      (universalCyclicCoefficientRelation282 R m n B k (j, a)) =
      commutingMatrixEvaluation282 M hM (monomial (B j) 1) a k -
        (Pi.single j 1 : Fin n → A) a := by
  classical
  let f := commutingMatrixSpecialization280 R m n M hM
  have hMN : ∀ i, M i = (universalMultiplicationMatrix280 R m n i).map f.toRingHom := by
    intro i
    ext a b
    exact (commutingMatrixSpecialization_entry280 R m n M hM i a b).symm
  have hnat := commutingMatrixEvaluation_map282
    (universalMultiplicationMatrix280 R m n)
    (universalMultiplicationMatrix_commute280 R m n) f.toRingHom M hM hMN
    (monomial (B j) 1)
  simp only [MvPolynomial.map_monomial, map_one] at hnat
  have he := congrArg (fun T : Matrix (Fin n) (Fin n) A => T a k) hnat
  change commutingMatrixEvaluation282 M hM (monomial (B j) 1) a k =
    f (commutingMatrixEvaluation282 (universalMultiplicationMatrix280 R m n)
      (universalMultiplicationMatrix_commute280 R m n) (monomial (B j) 1) a k) at he
  change f (_ - _) = _
  rw [map_sub, ← he]
  congr 1
  by_cases haj : a = j
  · simp [Pi.single_apply, apply_ite, haj]
  · simp [Pi.single_apply, apply_ite, haj]

lemma cyclicCoefficientIdeal_le_ker283
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A)) :
    universalCyclicCoefficientIdeal282 R m n B k ≤
      RingHom.ker (commutingMatrixSpecialization280 R m n M.matrices M.commute).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨j, a⟩, rfl⟩
  change commutingMatrixSpecialization280 R m n M.matrices M.commute
    (universalCyclicCoefficientRelation282 R m n B k (j, a)) = 0
  rw [universalCyclicRelation_specialization283]
  have h := congrFun (M.cyclic j) a
  rw [commutingMatrixPolynomialAction_apply282, Matrix.mulVec_single_one] at h
  exact sub_eq_zero.mpr h

def cyclicCoefficientSpecialization283
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A)) :
    UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A :=
  Ideal.Quotient.liftₐ (universalCyclicCoefficientIdeal282 R m n B k)
    (commutingMatrixSpecialization280 R m n M.matrices M.commute)
    (fun x hx => RingHom.mem_ker.mp (cyclicCoefficientIdeal_le_ker283 R m n B k M hx))

lemma cyclicCoefficientSpecialization_entry283
    (M : CyclicCommutingMatrixPoint283 m n B k (A := A)) (i : Fin m) (a b : Fin n) :
    cyclicCoefficientSpecialization283 R m n B k M
      (universalCyclicMultiplicationMatrix282 R m n B k i a b) = M.matrices i a b := by
  change (Ideal.Quotient.lift (universalCyclicCoefficientIdeal282 R m n B k)
    (commutingMatrixSpecialization280 R m n M.matrices M.commute).toRingHom
    (fun x hx => RingHom.mem_ker.mp (cyclicCoefficientIdeal_le_ker283 R m n B k M hx)))
      (Ideal.Quotient.mk (universalCyclicCoefficientIdeal282 R m n B k)
        (universalMultiplicationMatrix280 R m n i a b)) = _
  exact (Ideal.Quotient.lift_mk _ _ _).trans
    (commutingMatrixSpecialization_entry280 R m n M.matrices M.commute i a b)

lemma cyclicCoefficient_hom_ext283
    {f g : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A}
    (h : ∀ i a b, f (universalCyclicMultiplicationMatrix282 R m n B k i a b) =
      g (universalCyclicMultiplicationMatrix282 R m n B k i a b)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply commutingMatrixCoefficient_hom_ext280 R m n
  exact h

private lemma commutingMatrixAction_coordinate283
    {C : Type u} [CommRing C] {m n : ℕ}
    (M : Fin m → Matrix (Fin n) (Fin n) C)
    (hM : ∀ i j, M i * M j = M j * M i)
    (p : MvPolynomial (Fin m) C) (k a : Fin n) (w : Fin n → C)
    (h : commutingMatrixPolynomialAction282 M hM p (Pi.single k 1) = w) :
    commutingMatrixEvaluation282 M hM p a k = w a := by
  classical
  have hc := congrFun h a
  rw [commutingMatrixPolynomialAction_apply282, Matrix.mulVec_single_one] at hc
  exact hc

private lemma mappedMatrix_commute283
    {C D : Type u} [CommRing C] [CommRing D] {m n : ℕ}
    (f : C →+* D) (M : Fin m → Matrix (Fin n) (Fin n) C)
    (hM : ∀ i j, M i * M j = M j * M i) (i j : Fin m) :
    (M i).map f * (M j).map f = (M j).map f * (M i).map f := by
  have h := congrArg f.mapMatrix (hM i j)
  simpa only [RingHom.mapMatrix_apply, Matrix.map_mul] using h

private lemma mappedMatrix_cyclic283
    {C D : Type u} [CommRing C] [CommRing D] {m n : ℕ}
    (f : C →+* D) (M : Fin m → Matrix (Fin n) (Fin n) C)
    (hM : ∀ i j, M i * M j = M j * M i)
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (hcyc : ∀ j, commutingMatrixPolynomialAction282 M hM
      (monomial (B j) 1) (Pi.single k 1) = Pi.single j 1) (j : Fin n) :
    commutingMatrixPolynomialAction282 (fun i => (M i).map f)
      (mappedMatrix_commute283 f M hM)
      (monomial (B j) 1) (Pi.single k 1) = Pi.single j 1 := by
  classical
  have hnat := commutingMatrixEvaluation_map282 (R := C) (S := D)
    M hM f (fun i => (M i).map f) (mappedMatrix_commute283 f M hM)
    (fun _ => rfl) (monomial (B j) 1)
  simp only [MvPolynomial.map_monomial, map_one] at hnat
  rw [commutingMatrixPolynomialAction_apply282, Matrix.mulVec_single_one, hnat]
  funext a
  have h := commutingMatrixAction_coordinate283 (C := C) (m := m) (n := n)
    M hM (monomial (B j) 1) k a (Pi.single j 1) (hcyc j)
  change f (commutingMatrixEvaluation282 M hM (monomial (B j) 1) a k) =
    (Pi.single j 1 : Fin n → D) a
  rw [h]
  by_cases haj : a = j
  · simp [Pi.single_apply, apply_ite, haj]
  · simp [Pi.single_apply, apply_ite, haj]

private def mappedCyclicMatrixPoint283
    {C D : Type u} [CommRing C] [CommRing D] {m n : ℕ}
    (f : C →+* D) (M : Fin m → Matrix (Fin n) (Fin n) C)
    (hM : ∀ i j, M i * M j = M j * M i)
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (hcyc : ∀ j, commutingMatrixPolynomialAction282 M hM
      (monomial (B j) 1) (Pi.single k 1) = Pi.single j 1) :
    CyclicCommutingMatrixPoint283 m n B k (A := D) where
  matrices i := (M i).map f
  commute := mappedMatrix_commute283 f M hM
  cyclic := mappedMatrix_cyclic283 f M hM B k hcyc

private def actualInferredCoefficientPoint283
    (f : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) :=
  mappedCyclicMatrixPoint283
    (C := UniversalCyclicCoefficientAlgebra282 R m n B k) (D := A) (m := m) (n := n)
    f.toRingHom (universalCyclicMultiplicationMatrix282 R m n B k)
    (universalCyclicMultiplicationMatrix_commute282 R m n B k) B k
    (universalCyclicPolynomialAction_monomial282 R m n B k)

def cyclicCoefficientPoint283
    (f : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) :
    CyclicCommutingMatrixPoint283 m n B k (A := A) :=
  actualInferredCoefficientPoint283 R m n B k f

def cyclicCoefficientPointEquiv283 :
    (UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) ≃
      CyclicCommutingMatrixPoint283 m n B k (A := A) where
  toFun := cyclicCoefficientPoint283 R m n B k
  invFun := cyclicCoefficientSpecialization283 R m n B k
  left_inv f := by
    apply cyclicCoefficient_hom_ext283 R m n B k
    intro i a b
    exact cyclicCoefficientSpecialization_entry283 R m n B k _ i a b
  right_inv M := by
    apply CyclicCommutingMatrixPoint283.ext
    funext i a b
    exact cyclicCoefficientSpecialization_entry283 R m n B k M i a b

lemma cyclicCoefficientPoint_comp_entry283
    {D : Type u} [CommRing D] [Algebra R D]
    (f : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) (g : A →ₐ[R] D)
    (i : Fin m) (a b : Fin n) :
    (cyclicCoefficientPoint283 R m n B k (g.comp f)).matrices i a b =
      g ((cyclicCoefficientPoint283 R m n B k f).matrices i a b) := rfl

end PfaffianDescent
