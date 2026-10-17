import PfaffianDescent.FiniteBasisDeterminantOverlap290
import PfaffianDescent.MonomialWholeIdealChartNaturality287
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
namespace PfaffianDescent
open MvPolynomial Module
open scoped TensorProduct
universe u v
variable {A : Type u} [CommRing A] {S : Type v} [CommRing S] [Algebra A S]
variable {m n : ℕ}

/-- The coordinate matrix of the candidate second monomial tuple in the first actual quotient basis. -/
def wholeIdealMonomialTransitionMatrix290
    (I : Ideal (MvPolynomial (Fin m) A))
    (b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I))
    (C : Fin n → (Fin m →₀ ℕ)) : Matrix (Fin n) (Fin n) A :=
  b.toMatrix (fun j => Ideal.Quotient.mk I (monomial (C j) 1))

def wholeIdealMonomialTransitionDet290
    (I : Ideal (MvPolynomial (Fin m) A))
    (b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I))
    (C : Fin n → (Fin m →₀ ℕ)) : A :=
  (wholeIdealMonomialTransitionMatrix290 I b C).det

lemma wholeIdealMonomialTransitionDet_isUnit_iff290
    (I : Ideal (MvPolynomial (Fin m) A))
    (b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I))
    (C : Fin n → (Fin m →₀ ℕ)) :
    IsUnit (wholeIdealMonomialTransitionDet290 I b C) ↔
      ∃ c : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I),
        ∀ j, c j = Ideal.Quotient.mk I (monomial (C j) 1) :=
  isUnit_coordinateDet_iff_basis290 b _

/-- The same whole quotient after arbitrary scalar change, with its induced first basis. -/
def wholeIdealScalarBasis290 (S : Type v) [CommRing S] [Algebra A S]
    (I : Ideal (MvPolynomial (Fin m) A))
    (b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I)) :
    Basis (Fin n) S (MvPolynomial (Fin m) S ⧸ I.map (MvPolynomial.map (algebraMap A S))) :=
  (Algebra.TensorProduct.basis S b).map (polynomialWholeIdealScalarExtension286 S I).toLinearEquiv

lemma wholeIdealScalarBasis_apply290
    (I : Ideal (MvPolynomial (Fin m) A))
    (b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I))
    (B : Fin n → (Fin m →₀ ℕ))
    (hb : ∀ j, b j = Ideal.Quotient.mk I (monomial (B j) 1)) (j : Fin n) :
    wholeIdealScalarBasis290 S I b j =
      Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap A S))) (monomial (B j) 1) := by
  change polynomialWholeIdealScalarExtension286 S I (Algebra.TensorProduct.basis S b j) = _
  rw [Algebra.TensorProduct.basis_apply, hb]
  simpa only [polynomialWholeIdealScalarExtension_tmul286, one_smul,
    MvPolynomial.map_monomial, map_one]

lemma wholeIdealScalarBasis_repr_mapped290
    (I : Ideal (MvPolynomial (Fin m) A))
    (b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I))
    (p : MvPolynomial (Fin m) A) (a : Fin n) :
    (wholeIdealScalarBasis290 S I b).repr
      (Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap A S)))
        (MvPolynomial.map (algebraMap A S) p)) a =
      algebraMap A S (b.repr (Ideal.Quotient.mk I p) a) := by
  have he : polynomialWholeIdealScalarExtension286 S I
      (1 ⊗ₜ[A] Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap A S)))
        (MvPolynomial.map (algebraMap A S) p) := by
    simpa only [one_smul] using polynomialWholeIdealScalarExtension_tmul286 S I 1 p
  rw [← he]
  change (Algebra.TensorProduct.basis S b).repr
      ((polynomialWholeIdealScalarExtension286 S I).symm
        (polynomialWholeIdealScalarExtension286 S I (1 ⊗ₜ[A] Ideal.Quotient.mk I p))) a = _
  rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.basis_repr_tmul]
  simp

lemma wholeIdealMonomialTransitionMatrix_baseChange290
    (I : Ideal (MvPolynomial (Fin m) A))
    (b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I))
    (C : Fin n → (Fin m →₀ ℕ)) :
    wholeIdealMonomialTransitionMatrix290
        (I.map (MvPolynomial.map (algebraMap A S))) (wholeIdealScalarBasis290 S I b) C =
      (wholeIdealMonomialTransitionMatrix290 I b C).map (algebraMap A S) := by
  ext a j
  change (wholeIdealScalarBasis290 S I b).repr
      (Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap A S))) (monomial (C j) 1)) a = _
  have hp : MvPolynomial.map (algebraMap A S) (monomial (C j) 1) = monomial (C j) 1 := by
    rw [MvPolynomial.map_monomial, map_one]
  rw [← hp, wholeIdealScalarBasis_repr_mapped290]
  rfl

lemma wholeIdealMonomialTransitionDet_baseChange290
    (I : Ideal (MvPolynomial (Fin m) A))
    (b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I))
    (C : Fin n → (Fin m →₀ ℕ)) :
    wholeIdealMonomialTransitionDet290
        (I.map (MvPolynomial.map (algebraMap A S))) (wholeIdealScalarBasis290 S I b) C =
      algebraMap A S (wholeIdealMonomialTransitionDet290 I b C) := by
  rw [wholeIdealMonomialTransitionDet290, wholeIdealMonomialTransitionMatrix_baseChange290]
  exact ((algebraMap A S).map_det _).symm

/-- Exact second-chart condition after arbitrary base change; no flatness assumption. -/
lemma wholeIdealSecondMonomialBasis_baseChange_iff290
    (I : Ideal (MvPolynomial (Fin m) A))
    (b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I))
    (C : Fin n → (Fin m →₀ ℕ)) :
    (∃ c : Basis (Fin n) S (MvPolynomial (Fin m) S ⧸ I.map (MvPolynomial.map (algebraMap A S))),
      ∀ j, c j = Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap A S)))
        (monomial (C j) 1)) ↔
      IsUnit (algebraMap A S (wholeIdealMonomialTransitionDet290 I b C)) := by
  rw [← wholeIdealMonomialTransitionDet_isUnit_iff290
      (I.map (MvPolynomial.map (algebraMap A S))) (wholeIdealScalarBasis290 S I b) C,
    wholeIdealMonomialTransitionDet_baseChange290]

/-- Localization away from the constructed determinant gives the actual second monomial basis
of the original whole ideal's extension. -/
lemma wholeIdealSecondMonomialBasis_localization290
    (I : Ideal (MvPolynomial (Fin m) A))
    (b : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ I))
    (C : Fin n → (Fin m →₀ ℕ))
    [IsLocalization.Away (wholeIdealMonomialTransitionDet290 I b C) S] :
    ∃ c : Basis (Fin n) S (MvPolynomial (Fin m) S ⧸ I.map (MvPolynomial.map (algebraMap A S))),
      ∀ j, c j = Ideal.Quotient.mk (I.map (MvPolynomial.map (algebraMap A S)))
        (monomial (C j) 1) :=
  (wholeIdealSecondMonomialBasis_baseChange_iff290 (S := S) I b C).mpr
    (IsLocalization.Away.algebraMap_isUnit (S := S) _)

variable (B C : Fin n → (Fin m →₀ ℕ))

def monomialWholeIdealChartTransitionDet290 (x : MonomialWholeIdealChart287 (A := A) B) : A :=
  wholeIdealMonomialTransitionDet290 x.val (monomialWholeIdealChartBasis287 B x) C

/-- Principal determinant locus inside the represented first monomial chart. -/
def MonomialWholeIdealChartOverlap290 :=
  {x : MonomialWholeIdealChart287 (A := A) B //
    IsUnit (monomialWholeIdealChartTransitionDet290 B C x)}

/-- The overlap is equivalent to having both genuine monomial bases on the same literal ideal. -/
def monomialWholeIdealChartOverlapEquiv290 :
    MonomialWholeIdealChartOverlap290 (A := A) B C ≃
      {x : MonomialWholeIdealChart287 (A := A) B //
        ∃ c : Basis (Fin n) A (MvPolynomial (Fin m) A ⧸ x.val),
          ∀ j, c j = Ideal.Quotient.mk x.val (monomial (C j) 1)} where
  toFun x := ⟨x.val,
    (wholeIdealMonomialTransitionDet_isUnit_iff290 x.val.val
      (monomialWholeIdealChartBasis287 B x.val) C).mp x.property⟩
  invFun x := ⟨x.val,
    (wholeIdealMonomialTransitionDet_isUnit_iff290 x.val.val
      (monomialWholeIdealChartBasis287 B x.val) C).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma monomialWholeIdealChartTransitionDet_map290
    {D : Type v} [CommRing D] (k : Fin n) (hk : B k = 0)
    (f : A →+* D) (x : MonomialWholeIdealChart287 (A := A) B) :
    monomialWholeIdealChartTransitionDet290 B C (monomialWholeIdealChartMap287 B k hk f x) =
      f (monomialWholeIdealChartTransitionDet290 B C x) := by
  letI : Algebra A D := f.toAlgebra
  let y := monomialWholeIdealChartMap287 B k hk f x
  have hb : monomialWholeIdealChartBasis287 B y =
      wholeIdealScalarBasis290 D x.val (monomialWholeIdealChartBasis287 B x) := by
    apply DFunLike.ext
    intro j
    exact (monomialWholeIdealChartBasis_apply287 B y j).trans
      (wholeIdealScalarBasis_apply290 (S := D) x.val
        (monomialWholeIdealChartBasis287 B x) B
        (monomialWholeIdealChartBasis_apply287 B x) j).symm
  change wholeIdealMonomialTransitionDet290 y.val (monomialWholeIdealChartBasis287 B y) C = _
  rw [hb]
  exact wholeIdealMonomialTransitionDet_baseChange290 (S := D) x.val
    (monomialWholeIdealChartBasis287 B x) C

/-- The overlap map retains the original entire ideal map and derives the new unit condition. -/
def monomialWholeIdealChartOverlapMap290
    {D : Type v} [CommRing D] (k : Fin n) (hk : B k = 0) (f : A →+* D)
    (x : MonomialWholeIdealChartOverlap290 (A := A) B C) :
    MonomialWholeIdealChartOverlap290 (A := D) B C := by
  refine ⟨monomialWholeIdealChartMap287 B k hk f x.val, ?_⟩
  rw [monomialWholeIdealChartTransitionDet_map290 B C k hk f x.val]
  exact x.property.map f

end PfaffianDescent
