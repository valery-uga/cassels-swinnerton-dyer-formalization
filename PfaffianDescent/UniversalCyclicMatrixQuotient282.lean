import PfaffianDescent.UniversalCommutingMatrixCoefficients280
import PfaffianDescent.CyclicPolynomialActionFreeQuotient281
import PfaffianDescent.CommutingMatrixPolynomialAction282

/-! Actual cyclic coefficient relations in the universal commuting-matrix
algebra. The quotient supplies its own commuting matrices and polynomial
action. Primitive coefficient relations yield a basis for the entire
ambient polynomial action-kernel quotient, with no freeness premise. -/
noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)

def universalCyclicCoefficientRelation282 (q : Fin n × Fin n) :
    CommutingMatrixCoefficientAlgebra280 R m n :=
  commutingMatrixEvaluation282 (universalMultiplicationMatrix280 R m n)
    (universalMultiplicationMatrix_commute280 R m n) (monomial (B q.1) 1) q.2 k -
    (Pi.single q.1 1 : Fin n → CommutingMatrixCoefficientAlgebra280 R m n) q.2

def universalCyclicCoefficientIdeal282 :
    Ideal (CommutingMatrixCoefficientAlgebra280 R m n) :=
  Ideal.span (Set.range (universalCyclicCoefficientRelation282 R m n B k))

abbrev UniversalCyclicCoefficientAlgebra282 :=
  CommutingMatrixCoefficientAlgebra280 R m n ⧸ universalCyclicCoefficientIdeal282 R m n B k

lemma universalCyclicCoefficientIdeal_fg282 :
    (universalCyclicCoefficientIdeal282 R m n B k).FG := by
  change (Submodule.span (CommutingMatrixCoefficientAlgebra280 R m n)
    (Set.range (universalCyclicCoefficientRelation282 R m n B k))).FG
  exact Submodule.fg_span (Set.finite_range _)

lemma universalCyclicCoefficientAlgebra_finitePresentation282 :
    Algebra.FinitePresentation R (UniversalCyclicCoefficientAlgebra282 R m n B k) := by
  letI : Algebra.FinitePresentation R (CommutingMatrixCoefficientAlgebra280 R m n) :=
    commutingMatrixCoefficientAlgebra_finitePresentation280 R m n
  exact Algebra.FinitePresentation.quotient (R := R)
    (universalCyclicCoefficientIdeal_fg282 R m n B k)

def universalCyclicMultiplicationMatrix282 (i : Fin m) :
    Matrix (Fin n) (Fin n) (UniversalCyclicCoefficientAlgebra282 R m n B k) :=
  (universalMultiplicationMatrix280 R m n i).map
    (Ideal.Quotient.mk (universalCyclicCoefficientIdeal282 R m n B k))

lemma universalCyclicMultiplicationMatrix_commute282 (i j : Fin m) :
    universalCyclicMultiplicationMatrix282 R m n B k i *
        universalCyclicMultiplicationMatrix282 R m n B k j =
      universalCyclicMultiplicationMatrix282 R m n B k j *
        universalCyclicMultiplicationMatrix282 R m n B k i := by
  have h := congrArg
    (Ideal.Quotient.mk (universalCyclicCoefficientIdeal282 R m n B k)).mapMatrix
    (universalMultiplicationMatrix_commute280 R m n i j)
  simpa only [map_mul, RingHom.mapMatrix_apply, universalCyclicMultiplicationMatrix282] using h

def universalCyclicPolynomialAction282 :
    MvPolynomial (Fin m) (UniversalCyclicCoefficientAlgebra282 R m n B k) →ₐ[
      UniversalCyclicCoefficientAlgebra282 R m n B k]
        Module.End (UniversalCyclicCoefficientAlgebra282 R m n B k)
          (Fin n → UniversalCyclicCoefficientAlgebra282 R m n B k) :=
  commutingMatrixPolynomialAction282 (universalCyclicMultiplicationMatrix282 R m n B k)
    (universalCyclicMultiplicationMatrix_commute282 R m n B k)

private lemma cyclicMatrixQuotient_monomial282
    {A : Type u} [CommRing A] {m n : ℕ}
    (M : Fin m → Matrix (Fin n) (Fin n) A)
    (hM : ∀ i j, M i * M j = M j * M i)
    (I : Ideal A)
    (N : Fin m → Matrix (Fin n) (Fin n) (A ⧸ I))
    (hN : ∀ i j, N i * N j = N j * N i)
    (hMN : ∀ i, N i = (M i).map (Ideal.Quotient.mk I))
    (B : Fin n → (Fin m →₀ ℕ)) (k j : Fin n)
    (hmem : ∀ a, commutingMatrixEvaluation282 M hM (monomial (B j) 1) a k -
      (Pi.single j 1 : Fin n → A) a ∈ I) :
    commutingMatrixPolynomialAction282 N hN (monomial (B j) 1) (Pi.single k 1) =
      Pi.single j 1 := by
  classical
  let f : A →+* (A ⧸ I) := Ideal.Quotient.mk I
  have hnat := commutingMatrixEvaluation_map282 (R := A) (S := A ⧸ I)
    M hM f N hN hMN (monomial (B j) 1)
  simp only [MvPolynomial.map_monomial, map_one] at hnat
  rw [commutingMatrixPolynomialAction_apply282, Matrix.mulVec_single_one, hnat]
  funext a
  change f (commutingMatrixEvaluation282 M hM (monomial (B j) 1) a k) =
    (Pi.single j 1 : Fin n → A ⧸ I) a
  have hz : f (commutingMatrixEvaluation282 M hM (monomial (B j) 1) a k -
      (Pi.single j 1 : Fin n → A) a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hmem a)
  rw [map_sub] at hz
  rw [sub_eq_zero.mp hz]
  by_cases haj : a = j
  · simp [Pi.single_apply, apply_ite, haj]
  · simp [Pi.single_apply, apply_ite, haj]

lemma universalCyclicPolynomialAction_monomial282 (j : Fin n) :
    universalCyclicPolynomialAction282 R m n B k (monomial (B j) 1) (Pi.single k 1) =
      Pi.single j 1 := by
  apply cyclicMatrixQuotient_monomial282
    (A := CommutingMatrixCoefficientAlgebra280 R m n)
    (universalMultiplicationMatrix280 R m n)
    (universalMultiplicationMatrix_commute280 R m n)
    (universalCyclicCoefficientIdeal282 R m n B k)
    (universalCyclicMultiplicationMatrix282 R m n B k)
    (universalCyclicMultiplicationMatrix_commute282 R m n B k)
    (fun _ => rfl) B k j
  intro a
  exact Ideal.subset_span ⟨(j, a), rfl⟩

def universalCyclicWholeAmbientIdeal282 :
    Ideal (MvPolynomial (Fin m) (UniversalCyclicCoefficientAlgebra282 R m n B k)) :=
  RingHom.ker (universalCyclicPolynomialAction282 R m n B k).toRingHom

private abbrev nativePolynomialIdealQuotient282
    {A : Type u} [CommRing A] (m : ℕ) (I : Ideal (MvPolynomial (Fin m) A)) : Type u :=
  @HasQuotient.Quotient (MvPolynomial (Fin m) A) (Ideal (MvPolynomial (Fin m) A))
    (@Ideal.instHasQuotient (MvPolynomial (Fin m) A)
      (inferInstance : Ring (MvPolynomial (Fin m) A))) I

private lemma nativePolynomialIdealQuotient_eq282
    {A : Type u} [CommRing A] (m : ℕ) (I : Ideal (MvPolynomial (Fin m) A)) :
    nativePolynomialIdealQuotient282 m I = (MvPolynomial (Fin m) A ⧸ I) := rfl

abbrev UniversalCyclicWholeAmbientQuotient282 : Type u :=
  nativePolynomialIdealQuotient282 (A := UniversalCyclicCoefficientAlgebra282 R m n B k) m
    (universalCyclicWholeAmbientIdeal282 R m n B k)

private def nativeCyclicPolynomialMonomialBasis282
    {A : Type u} [CommRing A] {m n : ℕ}
    (rho : MvPolynomial (Fin m) A →ₐ[A] Module.End A (Fin n → A))
    (v : Fin n → A) (B : Fin n → (Fin m →₀ ℕ))
    (hB : ∀ j, rho (monomial (B j) 1) v = Pi.single j 1) :
    Basis (Fin n) A (nativePolynomialIdealQuotient282 m (RingHom.ker rho.toRingHom)) :=
  cyclicPolynomialQuotientMonomialBasis281 (R := A) rho v B hB

private lemma nativeCyclicPolynomialMonomialBasis_apply282
    {A : Type u} [CommRing A] {m n : ℕ}
    (rho : MvPolynomial (Fin m) A →ₐ[A] Module.End A (Fin n → A))
    (v : Fin n → A) (B : Fin n → (Fin m →₀ ℕ))
    (hB : ∀ j, rho (monomial (B j) 1) v = Pi.single j 1) (j : Fin n) :
    nativeCyclicPolynomialMonomialBasis282 rho v B hB j =
      Ideal.Quotient.mk (RingHom.ker rho.toRingHom) (monomial (B j) 1) :=
  cyclicPolynomialQuotientMonomialBasis_apply281 (R := A) rho v B hB j

private lemma nativeCyclicPolynomialQuotient_free_finite282
    {A : Type u} [CommRing A] {m n : ℕ}
    (rho : MvPolynomial (Fin m) A →ₐ[A] Module.End A (Fin n → A))
    (v : Fin n → A) (B : Fin n → (Fin m →₀ ℕ))
    (hB : ∀ j, rho (monomial (B j) 1) v = Pi.single j 1) :
    Module.Free A (nativePolynomialIdealQuotient282 m (RingHom.ker rho.toRingHom)) ∧
      Module.Finite A (nativePolynomialIdealQuotient282 m (RingHom.ker rho.toRingHom)) :=
  cyclicPolynomialQuotient_free_finite281 (R := A) rho v B hB

private def actualInferredNativeBasis282 :=
  nativeCyclicPolynomialMonomialBasis282 (A := UniversalCyclicCoefficientAlgebra282 R m n B k)
    (universalCyclicPolynomialAction282 R m n B k)
    (Pi.single k 1) B (universalCyclicPolynomialAction_monomial282 R m n B k)

private def actualOriginalWholeBasisType282 : Type u :=
  Basis (Fin n) (UniversalCyclicCoefficientAlgebra282 R m n B k)
    (UniversalCyclicWholeAmbientQuotient282 R m n B k)

private def actualOriginalWholeBasisConversion282 : actualOriginalWholeBasisType282 R m n B k :=
  actualInferredNativeBasis282 R m n B k

private def actualInferredNativeFreeFinite282 :=
  nativeCyclicPolynomialQuotient_free_finite282 (A := UniversalCyclicCoefficientAlgebra282 R m n B k)
    (universalCyclicPolynomialAction282 R m n B k)
    (Pi.single k 1) B (universalCyclicPolynomialAction_monomial282 R m n B k)

private def actualInferredNativeBasis_apply282 (j : Fin n) :=
  nativeCyclicPolynomialMonomialBasis_apply282 (A := UniversalCyclicCoefficientAlgebra282 R m n B k)
    (universalCyclicPolynomialAction282 R m n B k)
    (Pi.single k 1) B (universalCyclicPolynomialAction_monomial282 R m n B k) j

def universalCyclicWholeAmbientMonomialBasis282 :
    Basis (Fin n) (UniversalCyclicCoefficientAlgebra282 R m n B k)
      (UniversalCyclicWholeAmbientQuotient282 R m n B k) :=
  actualOriginalWholeBasisConversion282 R m n B k

private def polynomialDomainCommRingFromAction282
    {A : Type u} [CommRing A] {m n : ℕ}
    (_rho : MvPolynomial (Fin m) A →ₐ[A] Module.End A (Fin n → A)) :
    CommRing (MvPolynomial (Fin m) A) := inferInstance

private def probeActionDomainCommRing282 :=
  polynomialDomainCommRingFromAction282
    (A := UniversalCyclicCoefficientAlgebra282 R m n B k) (m := m) (n := n)
    (universalCyclicPolynomialAction282 R m n B k)

private def probeActualNativeMk282 :=
  @Ideal.Quotient.mk
    (MvPolynomial (Fin m) (UniversalCyclicCoefficientAlgebra282 R m n B k))
    (probeActionDomainCommRing282 R m n B k).toRing
    (universalCyclicWholeAmbientIdeal282 R m n B k)
    (inferInstance : (universalCyclicWholeAmbientIdeal282 R m n B k).IsTwoSided)

private def probeActualNativeMkTarget282 (p : MvPolynomial (Fin m) (UniversalCyclicCoefficientAlgebra282 R m n B k)) :
    UniversalCyclicWholeAmbientQuotient282 R m n B k :=
  probeActualNativeMk282 R m n B k p


private def actualOriginalWholeBasisApplyProp282 (j : Fin n) : Prop :=
  @Eq (UniversalCyclicWholeAmbientQuotient282 R m n B k)
    (universalCyclicWholeAmbientMonomialBasis282 R m n B k j)
    (probeActualNativeMkTarget282 R m n B k
      (monomial (B j) 1 : MvPolynomial (Fin m) (UniversalCyclicCoefficientAlgebra282 R m n B k)))

private def actualOriginalWholeBasisApplyConversion282 (j : Fin n) :
    actualOriginalWholeBasisApplyProp282 R m n B k j :=
  actualInferredNativeBasis_apply282 R m n B k j

lemma universalCyclicWholeAmbientMonomialBasis_apply282 (j : Fin n) :
    universalCyclicWholeAmbientMonomialBasis282 R m n B k j =
      (@Ideal.Quotient.mk
        (MvPolynomial (Fin m) (UniversalCyclicCoefficientAlgebra282 R m n B k))
        (probeActionDomainCommRing282 R m n B k).toRing
        (universalCyclicWholeAmbientIdeal282 R m n B k)
        (inferInstance : (universalCyclicWholeAmbientIdeal282 R m n B k).IsTwoSided)
        (monomial (B j) 1 : MvPolynomial (Fin m) (UniversalCyclicCoefficientAlgebra282 R m n B k))) :=
  actualOriginalWholeBasisApplyConversion282 R m n B k j

lemma universalCyclicWholeAmbientQuotient_free_finite282 :
    Module.Free (UniversalCyclicCoefficientAlgebra282 R m n B k)
      (UniversalCyclicWholeAmbientQuotient282 R m n B k) ∧
    Module.Finite (UniversalCyclicCoefficientAlgebra282 R m n B k)
      (UniversalCyclicWholeAmbientQuotient282 R m n B k) :=
  actualInferredNativeFreeFinite282 R m n B k

end PfaffianDescent
