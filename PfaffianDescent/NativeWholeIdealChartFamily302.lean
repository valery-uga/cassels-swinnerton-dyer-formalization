import PfaffianDescent.WholeIdealEmbeddedScalarCartesian296
import PfaffianDescent.MonomialChartOverlapLocalization292

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory Module
universe u

private lemma wholeIdealChart_value_congr302 {A : Type u} [CommRing A] {m n : ℕ}
    {B : Fin n → (Fin m →₀ ℕ)} (x y : MonomialWholeIdealChart287 (A := A) B)
    (h : x = y) : x.val = y.val := congrArg Subtype.val h

private lemma coefficientWholeIdeal_natural302
    (R : Type u) [CommRing R] {A D : Type u} [CommRing A] [CommRing D]
    [Algebra R A] [Algebra R D] {m n : ℕ}
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) (hk : B k = 0)
    (p : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) (f : A →ₐ[R] D) :
    (cyclicCoefficientWholeIdealChartEquiv287 (A := D) B k R hk (f.comp p)).val =
      (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk p).val.map
        (MvPolynomial.map f.toRingHom) :=
  wholeIdealChart_value_congr302
    (cyclicCoefficientWholeIdealChartEquiv287 (A := D) B k R hk (f.comp p))
    (monomialWholeIdealChartMap287 B k hk f.toRingHom
      (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk p))
    (cyclicCoefficientWholeIdealChartEquiv_natural287 (A := A) (E := D) B k R hk p f)

private lemma nativeWholeIdealKernel_congr302 {A : Type u} [CommRing A] {m : ℕ}
    (I J : Ideal (MvPolynomial (Fin m) A)) (h : I = J) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).ker :=
  congrArg (fun K : Ideal (MvPolynomial (Fin m) A) =>
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).ker) h

/-- Classification is by the entire image of the original universal ideal. -/
lemma cyclicCoefficientWholeIdealChart_ideal302
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) (hk : B k = 0)
    (p : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) :
    (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk p).val =
      (universalCyclicWholeAmbientIdeal282 R m n B k).map (MvPolynomial.map p.toRingHom) := by
  have h := coefficientWholeIdeal_natural302 R
    (A := UniversalCyclicCoefficientAlgebra282 R m n B k) (D := A)
    (m := m) (n := n) B k hk
    (AlgHom.id R (UniversalCyclicCoefficientAlgebra282 R m n B k)) p
  rw [AlgHom.comp_id] at h
  exact h

/-- The native finite-flat point of an actual whole-ideal monomial chart. -/
def monomialWholeIdealNativeFamily302
    {A : Type u} [CommRing A] {m n : ℕ} (B : Fin n → (Fin m →₀ ℕ))
    (x : MonomialWholeIdealChart287 (A := A) B) :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n :=
  affineWholeQuotientHilbertPoint289 x.val (monomialWholeIdealChartBasis287 B x)

/-- Assemble the original native polynomial Cartesian base change while coefficient
objects, dictionaries, dimensions and the input point are still ordinary parameters. -/
private def nativePolynomialFamilyBaseChange302
    (C S : Type u) [CommRing C] [CommRing S] [Algebra C S] (m n : ℕ)
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap C (MvPolynomial (Fin m) C)))) n) :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap S (MvPolynomial (Fin m) S)))) n :=
  finiteFlatHilbertBaseChange195
    (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap C S))))
    (Spec.map (CommRingCat.ofHom (algebraMap S (MvPolynomial (Fin m) S))))
    (Spec.map (CommRingCat.ofHom (algebraMap C (MvPolynomial (Fin m) C))))
    (Spec.map (CommRingCat.ofHom (algebraMap C S)))
    (ambientPolynomialScalar_isCartesian296 (C := C) (S := S) (m := m)) n P

/-- Literal native pullback of universal289 along an arbitrary coefficient point. -/
def cyclicCoefficientUniversalFamilyPullback302
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] (m n : ℕ)
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)
    (p : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) :
    FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n := by
  letI : Algebra (UniversalCyclicCoefficientAlgebra282 R m n B k) A := p.toRingHom.toAlgebra
  exact nativePolynomialFamilyBaseChange302
    (UniversalCyclicCoefficientAlgebra282 R m n B k) A m n
    (universalCyclicAffineHilbertPoint289 R m n B k)

/-- Arbitrary coefficient classification agrees with the native whole embedded family. -/
lemma cyclicCoefficientUniversalFamily_classifies302
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) (hk : B k = 0)
    (p : UniversalCyclicCoefficientAlgebra282 R m n B k →ₐ[R] A) :
    cyclicCoefficientUniversalFamilyPullback302 R m n B k p =
      monomialWholeIdealNativeFamily302 B
        (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk p) := by
  letI : Algebra (UniversalCyclicCoefficientAlgebra282 R m n B k) A := p.toRingHom.toAlgebra
  apply Subtype.ext
  have h := wholeIdealEmbeddedScalar_kernel_comap296
    (C := UniversalCyclicCoefficientAlgebra282 R m n B k) (S := A)
    (m := m) (universalCyclicWholeAmbientIdeal282 R m n B k)
  have hi := cyclicCoefficientWholeIdealChart_ideal302 R (A := A) B k hk p
  exact h.trans (nativeWholeIdealKernel_congr302 (A := A) (m := m)
    ((universalCyclicWholeAmbientIdeal282 R m n B k).map (MvPolynomial.map p.toRingHom))
    (cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk p).val hi.symm)

/-- Every represented monomial whole ideal is the actual pullback of universal289. -/
lemma monomialWholeIdealNativeFamily_isUniversalPullback302
    (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A] {m n : ℕ}
    (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n) (hk : B k = 0)
    (x : MonomialWholeIdealChart287 (A := A) B) :
    cyclicCoefficientUniversalFamilyPullback302 R m n B k
      ((cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk).symm x) =
      monomialWholeIdealNativeFamily302 B x :=
  (cyclicCoefficientUniversalFamily_classifies302 R B k hk _).trans
    (congrArg (monomialWholeIdealNativeFamily302 B)
      ((cyclicCoefficientWholeIdealChartEquiv287 (A := A) B k R hk).apply_symm_apply x))

/-- The constructed quotient presentation retains the original whole ideal sheaf. -/
lemma actualAffineHilbertPoint_kernel_of_presentation302
    {A : Type u} [CommRing A] {m n : ℕ}
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n)
    (I : Ideal (MvPolynomial (Fin m) A))
    (e : P.val.subscheme ≅ Spec (.of (MvPolynomial (Fin m) A ⧸ I)))
    (h : P.val.subschemeι = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    P.val = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker :=
  P.val.ker_subschemeι.symm.trans
    ((congrArg (fun f : P.val.subscheme ⟶ Spec (.of (MvPolynomial (Fin m) A)) => f.ker) h).trans
      (Scheme.Hom.ker_comp_of_isIso e.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))))

/-- Native restriction of an actual195 point equals the literal extended quotient family. -/
lemma actualAffineHilbertPoint_baseChange_presentation302
    {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] {m n : ℕ}
    (P : FiniteFlatHilbertPoint195
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A)))) n)
    (I : Ideal (MvPolynomial (Fin m) A))
    (e : P.val.subscheme ≅ Spec (.of (MvPolynomial (Fin m) A ⧸ I)))
    (h : P.val.subschemeι = e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (b : Basis (Fin n) S
      (MvPolynomial (Fin m) S ⧸ I.map (MvPolynomial.map (algebraMap A S)))) :
    finiteFlatHilbertBaseChange195
      (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := Fin m) (algebraMap A S))))
      (Spec.map (CommRingCat.ofHom (algebraMap S (MvPolynomial (Fin m) S))))
      (Spec.map (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin m) A))))
      (Spec.map (CommRingCat.ofHom (algebraMap A S)))
      (ambientPolynomialScalar_isCartesian296 (C := A) (S := S) (m := m)) n P =
    affineWholeQuotientHilbertPoint289 (I.map (MvPolynomial.map (algebraMap A S))) b := by
  apply Subtype.ext
  exact (congrArg
    (fun J : (Spec (.of (MvPolynomial (Fin m) A))).IdealSheafData =>
      J.comap (Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap A S)))))
    (actualAffineHilbertPoint_kernel_of_presentation302 P I e h)).trans
    (wholeIdealEmbeddedScalar_kernel_comap296 (C := A) (S := S) I)

end PfaffianDescent
